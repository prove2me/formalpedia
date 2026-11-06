-- Prove2me | Theorems.Thm_DecodablePOMDP_theorem_1
-- name    : DecodablePOMDP.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:27:01.266211+00:00
-- url     : https://prove2.me/theorems/f3f26538-9e53-486a-9ff6-1517b912eed6
-- title:
--   Theorem 1 — quasipolynomial-time $\varepsilon$-optimal planning for $\rho$-decodable POMDPs (corrected: time bound at min(ε, 1))
-- statement:
--   There are universal constants $C_1,C_2,C_3>0$, a degree $k$, one Turing machine $M$ and one output map $f$ such that for every valid rational instance $I$ (a POMDP $\mathcal P$ with parameters $H,S,A,O$ and an accuracy $\varepsilon>0$):
--
--   1. the deterministic finite-state controller $f(I)$ satisfies
--   $$V^{f(I)}_{\mathcal P}\ \ge\ V^*_{\mathcal P}-\varepsilon,$$
--   where $V^*_{\mathcal P}$ is the supremum over all history-dependent randomised policies;
--   2. for every $\rho\in(0,1]$ for which $\mathcal P$ is $\rho$-decodable, $M$ started on the binary code of $I$ (of length $n$) halts with the code of $f(I)$ within $t$ steps, where, with $\varepsilon'=\min(\varepsilon,1)$,
--   $$t\ \le\ (n+2)^k\Big(\frac{C_1AOSH}{\varepsilon'}\Big)^{C_2\log(C_3H/\varepsilon')/\rho}.$$
--
--   For $\varepsilon\le1$ this is the paper's statement: a deterministic $\varepsilon$-optimal policy in time $\mathrm{poly}(\text{input size})\,(C_1AOSH/\varepsilon)^{C_2\log(C_3H/\varepsilon)/\rho}$, quasipolynomial for every fixed $\rho>0$, without filter stability.
--
--   Differences from the source:
--   - correction: running time poly(input size)·(C₁AOSH/ε)^{C₂ log(C₃H/ε)/ρ} for every ε > 0 → the time bound uses ε′ = min(ε, 1) in place of ε (the accuracy clause keeps every ε > 0); reason: as printed the claim is false: for any C₁, C₂, C₃ > 0 and any polynomial, take S = O = 1, H = 2, A > C₃/C₁ and ε ∈ (C₃H, C₁AOSH); this POMDP is ρ-decodable for every ρ ∈ (0, 1] (D = 1), the base is > 1 and the exponent C₂ log(C₃H/ε)/ρ → −∞ as ρ → 0, so the bound is < 1 for small ρ and no machine halts in fewer than one step; the paper proves the bound for 0 < ε ≤ 1 ((9), p.12), and for ε > 1 the algorithm run at ε′ = 1 is ε-accurate
--   - reading: "runs in time at most poly(input size)·(…)" (no machine model fixed) → number of steps of one Mathlib multi-stack Turing machine with Boolean alphabets (`HMBinPacking.OutputsWithin`), poly(input size) = (n + 2)^k; reason: the paper's poly(input size) and "input bit complexity" (A.9) are the bit model; the bound class is closed under polynomial overhead (raising it to a power multiplies k and C₂), so RAM or bit-operation models give the same statement
--   - reading: input P (real data) and ε → a rational instance written in binary (`encodeInstance`: dimensions first, every entry, then ε); time and output are constrained only on valid instances; reason: an algorithm in the bit model reads finitely many rationals; the input size counts every entry of µ₁, T, K, r and ε
--   - reading: "produces a deterministic policy" → outputs the code of a deterministic finite-state controller (memory sizes, action and update tables) and is judged by its policy; reason: this is the output of A.10; an explicit format is needed, otherwise a description of the optimal policy (e.g. the input) would count as output
--   - reading: "Let P be a ρ-decodable POMDP" (ρ in the bound) → ρ is not an input: the time bound holds for every ρ ∈ (0, 1] for which P is ρ-decodable, with one machine for all ρ; reason: the algorithm does not need ρ (it computes decoders by the LP of A.9); a bound for each admissible ρ is the paper's claim
--   - encoding: accuracy clause under "Let P be a ρ-decodable POMDP" → accuracy clause for every valid instance, with no decodability hypothesis; reason: every valid POMDP is (1/S)-decodable (uniform decoder), so the hypothesis excludes no instance
--   - encoding: V* = sup over all history-dependent randomised policies (mixtures over a seed) → supremum over behavioural randomised history policies; reason: mixtures over a private seed and behavioural policies induce the same trajectory laws, hence the same values
--   - encoding: "for some universal constants C₁, C₂, C₃ > 0"; log → ∃ C₁ C₂ C₃ > 0, ∃ k, ∃ M, ∃ f before every instance and every ρ; natural logarithm and real power; reason: universal constants and one algorithm for all inputs; a fixed base of log is absorbed into C₂
-- source:
--   Dobson, Jog, Shiu, Quasipolynomial-Time Planning for Decodable POMDPs (preprint, sha256 c1256cbe…3584b), Theorem 1, p.4

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_DecodablePOMDP_Value
import Definitions.Def_DecodablePOMDP_IsDecodable
import Definitions.Def_DecodablePOMDP_Instance
import Definitions.Def_DecodablePOMDP_Code
import Definitions.Def_DecodablePOMDP_Controller

namespace DecodablePOMDP

/-- **Theorem 1 (corrected: time bound at min(ε, 1)).** There are universal constants
`C₁, C₂, C₃ > 0`, a polynomial degree `k`, one Turing machine `M` and one output map `f` such that,
for every valid rational instance `I` (POMDP `P` and accuracy `ε > 0`):
1. the deterministic finite-state controller `f I` has value `V^{f I}_P ≥ V*_P − ε`, where `V*_P`
   is the supremum over all history-dependent randomised policies; and
2. for every `ρ ∈ (0, 1]` for which `P` is ρ-decodable, `M` started on the binary code of `I`
   halts with the code of `f I` within `t` steps, where
   `t ≤ (n + 2)^k (C₁ A O S H / ε′)^{C₂ log(C₃ H / ε′) / ρ}`, `n` the input length and
   `ε′ = min(ε, 1)`.

Dobson, Jog, Shiu, *Quasipolynomial-Time Planning for Decodable POMDPs* (preprint, sha256
c1256cbe…3584b), Theorem 1, p.4: "Let P be a ρ-decodable POMDP and let ε > 0. There is an
algorithm that produces a deterministic policy whose expected cumulative reward is within ε of the
optimal value, and which runs in time at most poly(input size) (C1AOSH/ε)^{C2 log(C3H/ε)/ρ} for
some universal constants C1, C2, C3 > 0."

**Formalization Note.**
* Correction: as printed the bound fails for `ε ∈ (C₃H, C₁AOSH)` (it tends to `0` as `ρ → 0` on a
  POMDP with `S = O = 1`, `H = 2`, decodable for every `ρ`); the time bound uses `ε′ = min(ε, 1)`,
  the range the paper's proof covers ((9), p.12). The accuracy clause keeps every `ε > 0`.
* Machine model: steps of a Mathlib multi-stack Turing machine (`HMBinPacking.OutputsWithin`); the
  bound class is closed under polynomial overhead, so a RAM or bit-operation model gives the same
  statement. Input: the binary code `encodeInstance`; poly(input size) is `(n + 2)^k`.
* Output: a deterministic finite-state controller (`Controller`), its policy as in A.10.
* `ρ` is not an input; the bound holds for every `ρ ∈ (0, 1]` for which `P` is ρ-decodable. Every
  valid POMDP is `(1/S)`-decodable, so "Let P be a ρ-decodable POMDP" excludes no instance from (1).
* `log` is the natural logarithm and the exponent is a real power. -/
theorem theorem_1 :
    ∃ C₁ C₂ C₃ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ 0 < C₃ ∧
    ∃ k : ℕ, ∃ M : Turing.TM2ComputableAux Bool Bool,
    ∃ f : (I : Instance) → Controller I.H I.A I.O,
    ∀ I : Instance, I.IsValid →
      optValue I.toPOMDP - (I.ε : ℝ) ≤ value I.toPOMDP (f I).policy ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → IsDecodable I.toPOMDP ρ →
        ∃ t : ℕ, HMBinPacking.OutputsWithin M (encodeInstance I) (encodeController (f I)) t ∧
          (t : ℝ) ≤ (((encodeInstance I).length : ℝ) + 2) ^ k *
            (C₁ * (I.A : ℝ) * (I.O : ℝ) * (I.S : ℝ) * (I.H : ℝ) / min (I.ε : ℝ) 1) ^
              (C₂ * Real.log (C₃ * (I.H : ℝ) / min (I.ε : ℝ) 1) / ρ) := by sorry

end DecodablePOMDP

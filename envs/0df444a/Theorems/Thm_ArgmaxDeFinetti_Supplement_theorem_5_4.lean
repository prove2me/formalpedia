-- Prove2me | Theorems.Thm_ArgmaxDeFinetti_Supplement_theorem_5_4
-- name    : ArgmaxDeFinetti.Supplement.theorem_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:46:10.567548+00:00
-- url     : https://prove2.me/theorems/ca937500-3b63-479a-aba0-68747278f0b4
-- title:
--   Theorem 5.4, p.40 — $D_{\mathrm{tr}}(\rho,\mathrm{SEP}(d,d))$ to additive $\varepsilon$, and weak membership, in time $\mathrm{poly}\cdot\exp(O((\sqrt d/\varepsilon)\log(2+\varepsilon\sqrt d)))$
-- statement:
--   There are absolute constants $C>0$ and $k\in\mathbb N$ such that:
--
--   1. one deterministic algorithm, given $d$, a rational $\varepsilon\in(0,1]$ and a state $\rho$ on $\mathbb C^d\otimes\mathbb C^d$ with complex-rational entries, outputs a rational number within $\varepsilon$ of the trace distance $D_{\mathrm{tr}}(\rho,\mathrm{SEP}(d,d))=\min_{\sigma\in\mathrm{SEP}(d,d)}\tfrac12\|\rho-\sigma\|_1$;
--   2. one deterministic algorithm, on the same input, outputs "separable" when $\rho\in\mathrm{SEP}(d,d)$ and "far" when $D_{\mathrm{tr}}(\rho,\mathrm{SEP}(d,d))\ge\varepsilon$;
--
--   and each halts within
--   $$
--   (B+2)^k\exp\!\Big(C\frac{\sqrt d}{\varepsilon}\log\big(2+\varepsilon\sqrt d\big)\Big)
--   $$
--   steps, $B$ the bit length of the input. Nothing is required of the second algorithm when $0<D_{\mathrm{tr}}(\rho,\mathrm{SEP})<\varepsilon$.
--
--   This is the first trace-norm weak-membership algorithm for the separable set whose running time is subexponential in the local dimension at constant error.
--
--   **Formalization Note** The algorithms are deterministic Turing machines with binary input and output; "in the same running time" is the same constants $C,k$ for both tasks.
--
--   Differences from the source:
--   - reading: "can be approximated … deterministically" (no machine model named) → one fixed deterministic Turing machine (BitMachine: Mathlib FinTM2 with binary input and output) for all inputs; input d, then the rational parameters, then the matrix entries as complex rationals; output a rational in lowest terms, resp. one bit; reason: the paper fixes no model; Theorem 1.7 speaks of the input bit complexity, i.e. the bit model
--   - reading: "up to a factor polynomial in the bit complexity of M" (resp. ρ) → (B + 2)^k with B the length of the whole input encoding (d, the rational parameters and the matrix); reason: Theorems 1.7–1.8 say "input bit complexity"; reading the rational parameters costs their own length, so the factor cannot depend on the matrix alone
--   - reading: exp(O((√d/ε) log(2 + ε√d))) → exp(C·(√d/ε)·log(2 + ε√d)) with C > 0 and k absolute, chosen before d, ε and the input; reason: the implied constant is universal (standing assumption, Table 1 caption)
--   - encoding: D_tr(ρ, SEP(d, d)) → the base distSet with DimFreeShadow.traceDistance (½∥·∥₁), an infimum over the nonempty set SEP(d, d); reason: definition (2.5); the infimum is attained but need not be stated
--   - encoding: explicitly given state ρ on ℂ^d ⊗ ℂ^d → a matrix of complex rationals that is a density operator (WildeQIT.IsDensityOperator); reason: Lean convention for explicit input
--   - encoding: ℂ^d (and ℂ^{dA}, ℂ^{dB}, n ≥ 1) → hypotheses 1 ≤ d (resp. 1 ≤ dA, 1 ≤ dB, 1 ≤ n); reason: excludes only empty spaces, where no state exists
-- source:
--   Jeronimo, Wu, Xu, Optimal Quantum de Finetti Theorems via Argmax Rounding, arXiv:2608.02590 (held version, sha256 fb339472…), Theorem 5.4, eqs. (5.16)–(5.17), p.40 (= Theorem 1.8, p.10)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_DimFreeShadow_traceDistance
import Definitions.Def_ArgmaxDeFinetti_hausdorff
import Definitions.Def_ArgmaxDeFinetti_Supplement_bext
import Definitions.Def_ArgmaxDeFinetti_Supplement_BitMachine

open Matrix

namespace ArgmaxDeFinetti

namespace Supplement

/-- **Theorem 5.4 (Subexponential trace-norm separability algorithm)**, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), p.40, eqs. (5.16)–(5.17)
(= Theorem 1.8, p.10). Let `ρ` be an explicitly given state on `ℂ^d ⊗ ℂ^d`. For every `ε ∈ (0, 1]`, the distance
`D_tr(ρ, SEP(d, d))` can be approximated to additive error `ε` deterministically, in time polynomial in the bit
complexity times `exp(O((√d/ε) log(2 + ε√d)))` (5.16). In the same running time one can distinguish `ρ ∈ SEP(d, d)`
from `D_tr(ρ, SEP(d, d)) ≥ ε` (5.17).

**Formalization Note**
* `D_tr(ρ, SEP(d, d))` is the base `distSet` with `DimFreeShadow.traceDistance` (`½∥·∥₁`), an infimum over the
  nonempty set `SEP(d, d)` (2.5).
* Algorithms are `BitMachine`s, one fixed machine for each task. Input: `d`, `ε`, then the entries of `ρ` as complex
  rationals (`encMat`); `ρ` is a density operator. Output: a rational within `ε` of the distance, resp. one bit
  (`true` = "separable", `false` = "at distance `≥ ε`"); nothing is required in the intervening regime.
* "Up to a factor polynomial in the bit complexity" is `(B + 2)^k` with `B` the length of the whole input; `C`, `k`
  are absolute, chosen before `d`, `ε` and `ρ`, and shared by both tasks ("in the same running time"). -/
theorem theorem_5_4 :
    ∃ (C : ℝ) (k : ℕ), 0 < C ∧
      (∃ A : BitMachine, ∀ (d : ℕ) (ρq : Matrix (Fin d × Fin d) (Fin d × Fin d) (ℚ × ℚ)) (ε : ℚ),
        1 ≤ d → 0 < ε → ε ≤ 1 → WildeQIT.IsDensityOperator (ρq.map ratC) →
          ∃ (q : ℚ) (T : ℕ), A.OutputsWithin (encNat d ++ encRat ε ++ encMat ρq) (encRat q) T ∧
            |(q : ℝ) - distSet DimFreeShadow.traceDistance (ρq.map ratC) (sepAB d d)| ≤ ε ∧
            (T : ℝ) ≤ subexpBound C k (encNat d ++ encRat ε ++ encMat ρq).length d ε) ∧
      (∃ A : BitMachine, ∀ (d : ℕ) (ρq : Matrix (Fin d × Fin d) (Fin d × Fin d) (ℚ × ℚ)) (ε : ℚ),
        1 ≤ d → 0 < ε → ε ≤ 1 → WildeQIT.IsDensityOperator (ρq.map ratC) →
          ∃ (b : Bool) (T : ℕ), A.OutputsWithin (encNat d ++ encRat ε ++ encMat ρq) [b] T ∧
            (ρq.map ratC ∈ sepAB d d → b = true) ∧
            ((ε : ℝ) ≤ distSet DimFreeShadow.traceDistance (ρq.map ratC) (sepAB d d) → b = false) ∧
            (T : ℝ) ≤ subexpBound C k (encNat d ++ encRat ε ++ encMat ρq).length d ε) := by sorry

end Supplement

end ArgmaxDeFinetti

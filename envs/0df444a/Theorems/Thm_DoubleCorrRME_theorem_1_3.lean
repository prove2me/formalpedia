-- Prove2me | Theorems.Thm_DoubleCorrRME_theorem_1_3
-- name    : DoubleCorrRME.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:57:10.996989+00:00
-- url     : https://prove2.me/theorems/74085e2f-e7d4-46ea-b8b8-79546cc9a3cb
-- title:
--   Theorem 1.3, p.2 — robust mean estimation under strong double corruption in $\tilde O(Nnd)$ time with error $O(\sqrt\alpha+\sqrt{\varepsilon/n}+\sqrt{(d+\log(1/\delta))/(Nn)})$
-- statement:
--   **Setting** (Problem 1, Definition 1.1). There are $N$ users; user $i$ holds $n$ samples $z_{i,1},\dots,z_{i,n}\in\mathbb R^d$, and all $Nn$ samples are i.i.d. from an unknown law $P$ with mean $\mu$ and covariance $\Sigma\preceq I_d$. An adversary that may examine the entire dataset chooses a set $B$ of at most $\varepsilon N$ users and replaces all their samples arbitrarily, and replaces at most $\alpha Nn$ further samples among the users outside $B$. The estimator sees only the corrupted data $\{x_{i,j}\}$.
--
--   **Theorem.** There are universal constants $c,C,C_T>0$, $K\in\mathbb N$ and one program of the coin-tape real RAM such that for all $N$, $n,d\ge1$, $\varepsilon,\alpha\in(0,c)$ and $\delta\in(0,1)$ with $N\ge\log(1/\delta)$, on input $(N,n,d,\varepsilon,\alpha,\delta,x)$:
--
--   1. every run halts within $C_T\,Nnd\,\log^K(2+N+n+d+1/\delta)$ steps;
--   2. the output $\hat\mu$ is a measurable function of the coin tape;
--   3. for every law $P$ and every strong $(\varepsilon,\alpha)$-double-corruption adversary, with probability at least $1-\delta$,
--
--   $$\|\hat\mu-\mu\|_2\le C\Big(\sqrt\alpha+\sqrt{\frac\varepsilon n}+\sqrt{\frac{d+\log(1/\delta)}{Nn}}\Big).$$
--
--   The terms $\sqrt\alpha$ and $\sqrt{\varepsilon/n}$ are minimax optimal, and the last term is the sub-Gaussian rate with additive dependence on $\log(1/\delta)$; the running time is nearly linear in the input size.
--
--   **Formalization Note** The machine is a reading: the paper names none. The probability is the lower integral over the clean data of the coin-tape probability, meaningful for every adversary, measurable or not. $\tilde O$ hides polylogarithmic factors in $N,n,d,1/\delta$ only.
--
--   Differences from the source:
--   - reading: "there exists an algorithm (Algorithm 2) with running time Õ(Nnd)" → ∃ one admissible program of the coin-tape exact real RAM (input N, n, d, ε, α, δ, x) halting on every input and tape within C_T·N·n·d·log^K(2 + N + n + d + 1/δ) steps; reason: the paper names no machine; the weakest primitives the method needs; Õ hides polylog factors in N, n, d, 1/δ only, as the paper's accounting does
--   - reading: "with probability at least 1 − δ" → lower integral over the clean data of the coin-tape probability of the error event, for every adversary; the output is measurable in the tape; reason: meaningful for non-measurable adversaries; for a measurable adversary it is the joint probability
--   - encoding: Problem 1 law with mean µ and Σ ⪯ I_d → IsBoundedCovLaw D (MemLp id 2 and E⟨u, x − µ⟩² ≤ ∥u∥²), cleanLaw = Nn i.i.d. copies; reason: the mean and covariance exist exactly under a finite second moment
--   - encoding: strong (ε, α)-double-corruption adversary (Definition 1.1) → any map A with, for every clean z, some B, |B| ≤ εN, and at most αNn changed points outside B; reason: the adversary sees all clean data; a randomized adversary is a mixture of such maps
--   - encoding: "ε, α > 0 sufficiently small" and O(·) → ∃ c, C > 0 before every instance quantifier; 0 < ε, α < c; reason: meaning of the universal constants
--   - encoding: n samples per user in ℝ^d → 1 ≤ n, 1 ≤ d; reason: at n = 0 Lean's x/0 = 0 would make the bound C√α with no data, and at d = 0 there is nothing to estimate
-- source:
--   Aliakbarpour, Liu, Yin, Robust Mean Estimation Under Strong Double Corruption: Near-Linear Time and Sub-Gaussian Rate, STOC 2027 submission (manuscript sha256 49e26e5e…), Theorem 1.3, p.2 (PDF p.3), restated p.29 (PDF p.30); Problem 1 and Definition 1.1, p.1 (PDF p.2)

import Mathlib
import Definitions.Def_DoubleCorrRME_Model
import Definitions.Def_DoubleCorrRME_Machine
import Definitions.Def_DoubleCorrRME_InputLayout

open MeasureTheory

namespace DoubleCorrRME

/-- **Theorem 1.3** (main result), p.2 (PDF p.3), restated p.29 (PDF p.30); Problem 1 and
Definition 1.1, p.1 (PDF p.2).

Aliakbarpour, Liu, Yin, *Robust Mean Estimation Under Strong Double Corruption: Near-Linear Time
and Sub-Gaussian Rate*, STOC 2027 submission (manuscript sha256 49e26e5e…).

"Theorem 1.3. Let ε, α > 0 be sufficiently small, and let δ ∈ (0, 1). Let N ≥ log(1/δ). Under the
setting of Problem 1, there exists an algorithm (Algorithm 2) with running time Õ(Nnd) that, with
probability at least 1 − δ, outputs µ̂ ∈ ℝ^d satisfying
∥µ̂ − µ∥₂ ≤ O(√α + √(ε/n) + √((d + log(1/δ))/(Nn)))."

There are constants `c, C, C_T > 0`, `K ∈ ℕ` and one admissible program `P` such that for all
`N`, `n, d ≥ 1`, `ε, α ∈ (0, c)` and `δ ∈ (0, 1)` with `log(1/δ) ≤ N`, on input
`(N, n, d, ε, α, δ, x)`:
1. every coin tape and every dataset halts with `work ≤ C_T·N·n·d·log^K(2 + N + n + d + 1/δ)`;
2. the output is a measurable function of the tape;
3. for every law `P` on `ℝ^d` with finite second moment, mean `µ` and covariance `Σ ⪯ I_d`, and every
   strong `(ε, α)`-double-corruption adversary, the output satisfies
   `∥µ̂ − µ∥₂ ≤ C(√α + √(ε/n) + √((d + log(1/δ))/(Nn)))` with probability at least `1 − δ` (lower
   integral over the clean data of the tape probability).

**Formalization Note.**
* **Machine** (`Def_DoubleCorrRME_Machine`, a reading: the paper names none): an exact real RAM with
  rational literals, `+ − × ÷`, `√`, comparisons, indirect addressing, integer pointers and a fair
  coin, with unit cost per instruction; no floor, exp, log, power or Gaussian draw. The program takes
  `N, n, d, ε, α, δ` and the data as input (`goalInput`), as Algorithm 2 does, so one program serves
  every parameter value. The theorem asserts the existence of a program and does not refer to
  Algorithm 2.
* **Constants.** `c` ("sufficiently small"), `C` (the `O(·)`), `C_T` and `K` (`Õ`) are chosen before
  every instance quantifier. `Õ(Nnd)` hides a polylogarithmic factor in `N, n, d, 1/δ` only, not in
  `1/ε` or `1/α`; `2 +` keeps the logarithm positive. The time bound holds on every input and every
  tape (worst case).
* **Randomness and success.** The tape is a sequence of independent fair coins (`coinTape`). The
  success probability is the lower integral over the clean data `z ∼ P^{⊗Nn}` of the tape probability
  of the good event for the corrupted input `A(z)`; it is meaningful for every adversary, measurable
  or not, and for a measurable adversary it is the joint probability.
* **Adversary.** Any map of the whole clean dataset (it "may examine the entire dataset") such that for
  every `z` some `B` with `|B| ≤ εN` has at most `αNn` changed points outside `B`. It does not see
  the coins. A randomized adversary is a mixture of such maps.
* **Law.** `MemLp id 2` and `E⟨u, x − µ⟩² ≤ ‖u‖²` (`IsBoundedCovLaw`); without the finite second moment
  Lean's integral would be `0` and `Σ ⪯ I_d` vacuous.
* `n, d ≥ 1`: at `n = 0` Lean's `x/0 = 0` would turn the bound into `C√α` with no data, and at
  `d = 0` the time bound would be `0`. `N ≥ 1` follows from `log(1/δ) ≤ N` and `δ < 1`. Problem 1's
  range `α, ε < 0.5` is implied once `c ≤ 1/2`. `N ≥ log(1/δ)` is kept exactly as printed. -/
theorem theorem_1_3 :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∃ CT : ℝ, 0 < CT ∧ ∃ K : ℕ, ∃ P : Program, Admissible P ∧
      ∀ N n d : ℕ, 1 ≤ n → 1 ≤ d → ∀ ε α δ : ℝ, 0 < ε → ε < c → 0 < α → α < c →
        0 < δ → δ < 1 → Real.log (1 / δ) ≤ N →
        (∀ (x : Fin N → Fin n → Vec d) (ω : ℕ → Bool), ∃ t : ℕ,
          (run P (goalInput N n d ε α δ x) ω t).halted = true ∧
          ((run P (goalInput N n d ε α δ x) ω t).work : ℝ) ≤
            CT * N * n * d * Real.log (2 + N + n + d + 1 / δ) ^ K) ∧
        (∀ x : Fin N → Fin n → Vec d, Measurable fun ω => output P d (goalInput N n d ε α δ x) ω) ∧
        ∀ (D : Measure (Vec d)) [IsProbabilityMeasure D], IsBoundedCovLaw D →
          ∀ A : (Fin N → Fin n → Vec d) → (Fin N → Fin n → Vec d), IsDoubleAdversary ε α A →
            ENNReal.ofReal (1 - δ) ≤
              ∫⁻ z, coinTape {ω | ‖output P d (goalInput N n d ε α δ (A z)) ω - popMean D‖ ≤
                C * (Real.sqrt α + Real.sqrt (ε / n) +
                  Real.sqrt (((d : ℝ) + Real.log (1 / δ)) / ((N : ℝ) * n)))} ∂(cleanLaw N n D) := by sorry

end DoubleCorrRME

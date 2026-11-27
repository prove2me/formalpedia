-- Prove2me | Theorems.Thm_BosonicResources_theorem_3
-- name    : BosonicResources.theorem_3
-- status  : Open
-- author  : @Senrui Chen
-- created : 2026-11-27T06:34:31.610783+00:00
-- url     : https://prove2.me/theorems/62c2ecf9-52f8-5d2c-bdf7-5524bf7076b7
-- title:
--   Theorem 3: $\Omega(n^2/\varepsilon^2)$ copies are necessary with arbitrary measurements
-- statement:
--   Throughout, $\rho(\mu,\Sigma)$ denotes the $n$-mode Gaussian state with mean $\mu\in\mathbb R^{2n}$ and covariance matrix $\Sigma$, a real $2n\times 2n$ matrix; quadratures are ordered $(x_1,\dots,x_n,p_1,\dots,p_n)$ and the vacuum has covariance $\tfrac12 I$. A *learner on $N$ copies* is a POVM on the $N$-copy Hilbert space, possibly entangled across the copies, whose outcome is the estimate $\hat\rho$, a density operator. It *learns $\rho$ to trace distance $\varepsilon$* if, measured on $\rho^{\otimes N}$, its outcome satisfies $D_{\mathrm{tr}}(\hat\rho,\rho)=\tfrac12\|\hat\rho-\rho\|_1\le\varepsilon$ with probability at least $2/3$. A state is *pure* if it is a rank-one projector, and $\log$ is the natural logarithm.
--
--   There are universal constants $c>0$, $\varepsilon_0>0$, $E_0\in\mathbb R$ and $n_0\in\mathbb N$ such that the following holds for every $n\ge n_0$, every $\varepsilon\in(0,\varepsilon_0)$, every $N$ and every learner $P$ on $N$ copies.
--
--   1. If $P$ learns to trace distance $\varepsilon$ every zero-mean $n$-mode Gaussian state $\rho(0,\Sigma)$ with $\|\Sigma\|_{\mathrm{op}}\le E_0$, then $N\ge c\,n^{2}/\varepsilon^{2}$.
--   2. If $P$ learns to trace distance $\varepsilon$ every *pure* zero-mean $n$-mode Gaussian state $\rho(0,\Sigma)$ with $\|\Sigma\|_{\mathrm{op}}\le E_0$, then $N\ge c\,n^{2}/\big(\varepsilon^{2}\log(n/\varepsilon)\big)$.
--
--   In display form, the two lower bounds are
--
--   $$
--   N\ \ge\ c\,\frac{n^{2}}{\varepsilon^{2}}\quad\text{(zero-mean Gaussian states)},\qquad N\ \ge\ c\,\frac{n^{2}}{\varepsilon^{2}\log(n/\varepsilon)}\quad\text{(pure zero-mean Gaussian states)}.
--   $$
--
--   The theorem is the general lower bound of the paper: no measurement, Gaussian or not, entangled across the copies or not, learns $n$-mode Gaussian states with fewer than order $n^{2}/\varepsilon^{2}$ copies, and up to a logarithmic factor the same holds for pure states, which matches the upper bound of Theorem 5.
--
--   **Formalization Note** The same constants $c,\varepsilon_0,E_0,n_0$ serve both parts. $\Omega(\cdot)$ is a universal constant with thresholds $n_0$, $\varepsilon_0$ ("$\varepsilon$ upper bounded by a sufficiently small constant", proof of Theorem S5; Theorem S4 has $\varepsilon\le0.03$). $\log$ is the natural logarithm (App. A); for $n\ge1$ and $\varepsilon<1$ the argument $n/\varepsilon$ exceeds $1$. $\|\Sigma\|_{\mathrm{op}}\le E_0$ is encoded as positive semidefiniteness of $E_0\cdot I-\Sigma$. The learner is a POVM whose outcome is the estimate (`BosonicLearn.collectiveSuccess`); purity is `IsPure`.
-- source:
--   Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, What resources are needed for optimal learning of bosonic Gaussian states?, https://arxiv.org/abs/2603.18136, Sec. 3.2, Theorem 3; App. C.2.1, Theorem S5; App. C.2, Theorem S4

import Mathlib
import Definitions.Def_BosonicLearn_collectiveSuccess
import Definitions.Def_BosonicLearn_IsGaussianState
import Definitions.Def_BosonicResources_IsPure
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open BosonicLearn

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BosonicResources

/-- **Theorem 3 (Lower bound with arbitrary measurements).**
Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, *What resources are needed for optimal learning of bosonic
Gaussian states?*, arXiv:2603.18136, Theorem 3: "N = Ω(n²/ε²) copies are necessary to learn an n-mode Gaussian states ρ(µ,Σ) to ε trace distance
closeness with probability 2/3 using any POVM measurements, even with the promise that ‖Σ‖_op = O(1) and ρ has zero
mean. Furthermore, even if ρ is promised to be pure, N = Ω̃(n²/ε²) = Ω(n²/(ε² log(n/ε))) copies are still necessary."
Precise forms: Theorem S5 (App. C.2.1) and Theorem S4 (App. C.2, "ε ≤ 0.03", zero-mean pure states).

There are constants `c > 0`, `ε₀ > 0`, `E₀` and `n₀` such that for every `n ≥ n₀`, `ε ∈ (0, ε₀)`, every `N` and every
POVM on `N` copies (entangled across copies) whose outcome is the estimate:
1. if every zero-mean Gaussian state with `‖Σ‖_op ≤ E₀` is learned to trace distance `ε` with probability at least
   `2/3`, then `N ≥ c n²/ε²`;
2. if every pure zero-mean Gaussian state with `‖Σ‖_op ≤ E₀` is learned to trace distance `ε` with probability at
   least `2/3`, then `N ≥ c n²/(ε² log(n/ε))`.

**Formalization Note.** `Ω(·)` is a universal constant with thresholds `n₀`, `ε₀` ("ε upper bounded by a sufficiently
small constant", proof of Theorem S5; Theorem S4 has `ε ≤ 0.03`). `log` is the natural logarithm (App. A); for
`n ≥ 1` and `ε < 1` the argument `n/ε` exceeds `1`. `‖Σ‖_op ≤ E₀` is `E₀·I − Σ ⪰ 0`. -/
theorem theorem_3 :
    ∃ c : ℝ, 0 < c ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ E₀ : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ (N : ℕ) (P : FockPOVM (Fin N → Occupation (Fin n)) (State (Occupation (Fin n)))),
        ((∀ (ρ : State (Occupation (Fin n))) (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
            IsGaussianState ρ 0 S →
            (E₀ • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) - S).PosSemidef →
            ENNReal.ofReal (2 / 3) ≤ collectiveSuccess P ρ ε) →
          c * ((n : ℝ) ^ 2 / ε ^ 2) ≤ N) ∧
        ((∀ (ρ : State (Occupation (Fin n))) (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
            IsPure ρ → IsGaussianState ρ 0 S →
            (E₀ • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) - S).PosSemidef →
            ENNReal.ofReal (2 / 3) ≤ collectiveSuccess P ρ ε) →
          c * ((n : ℝ) ^ 2 / (ε ^ 2 * Real.log ((n : ℝ) / ε))) ≤ N) := by sorry

end BosonicResources

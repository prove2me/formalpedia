-- Prove2me | Theorems.Thm_BosonicResources_theorem_5
-- name    : BosonicResources.theorem_5
-- status  : Open
-- author  : @Senrui Chen
-- created : 2026-11-27T06:36:58.99582+00:00
-- url     : https://prove2.me/theorems/bd29c947-59c8-5d11-b6bc-6fcd9b5c7359
-- title:
--   Theorem 5: pure Gaussian states are learned with $\widetilde O(n^2/\varepsilon^2)$ copies by Gaussian measurements
-- statement:
--   Throughout, $\rho(\mu,\Sigma)$ denotes the $n$-mode Gaussian state with mean $\mu\in\mathbb R^{2n}$ and covariance matrix $\Sigma$, a real $2n\times 2n$ matrix; quadratures are ordered $(x_1,\dots,x_n,p_1,\dots,p_n)$ and the vacuum has covariance $\tfrac12 I$. A state is *pure* if it is a rank-one projector.
--
--   A *Gaussian (general-dyne) measurement with seed covariance $V$* is the POVM on one copy with outcomes $\xi\in\mathbb R^{2n}$ and elements $(2\pi)^{-n}\rho(\xi,V)\,d\xi$, the displaced copies of a Gaussian seed state with covariance $V$. An *adaptive single-copy scheme* measures the $N$ copies one at a time, and the POVM applied to the $t$-th copy may depend on the outcomes of the first $t-1$ measurements. An estimator is a possibly randomized map from the $N$ outcomes to a density operator $\hat\rho$, and the protocol *learns $\rho$ to trace distance $\varepsilon$* if $D_{\mathrm{tr}}(\hat\rho,\rho)=\tfrac12\|\hat\rho-\rho\|_1\le\varepsilon$ with probability at least $2/3$ over the outcomes and the randomness of the estimator. Here $\log$ is the natural logarithm.
--
--   There is a universal constant $C>0$ such that for every $n\ge1$, every $\varepsilon\in(0,1)$ and every $\bar E\ge16$ there exist an integer $N$ with
--
--   $$
--   N\ \le\ C\Big(\frac{n^{2}}{\varepsilon^{2}}+\big(n+\log\log\log\bar E\big)\log\log\bar E\Big),
--   $$
--
--   an adaptive single-copy scheme on $N$ copies all of whose measurements are Gaussian (general-dyne) measurements, and an estimator, which together learn to trace distance $\varepsilon$ every pure $n$-mode Gaussian state $\rho(\mu,\Sigma)$ with $\|\Sigma\|_{\mathrm{op}}\le\bar E$.
--
--   Together with the pure-state lower bound of Theorem 3, this shows that $\widetilde\Theta(n^{2}/\varepsilon^{2})$ copies are necessary and sufficient for learning pure Gaussian states, and that this is achieved by Gaussian measurements: non-Gaussian resources give essentially no advantage for pure Gaussian state tomography.
--
--   **Formalization Note** $O(\cdot)$ is one constant uniform in $n,\varepsilon,\bar E$. The bound is stated for $\bar E\ge16$, the range in which $\log\log\bar E$ and $\log\log\log\bar E$ are positive ($e^{e}<16$); a class with smaller $\bar E$ is contained in the class for $\bar E=16$. The protocol (scheme and estimator) is chosen before the state. $\|\Sigma\|_{\mathrm{op}}\le\bar E$ is encoded as positive semidefiniteness of $\bar E\cdot I-\Sigma$. The running-time claim of Theorem S8 is not part of the statement. Lean objects: a `BosonicLearn.AdaptiveScheme` with `IsGaussianScheme` (the seed may depend on the round and on earlier outcomes), a Markov-kernel estimator, `BosonicLearn.successProb` and `IsPure`.
-- source:
--   Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, What resources are needed for optimal learning of bosonic Gaussian states?, https://arxiv.org/abs/2603.18136, Sec. 3.3, Theorem 5, Eq. (4); App. D.1, Theorem S8

import Mathlib
import Definitions.Def_BosonicLearn_successProb
import Definitions.Def_BosonicLearn_IsGaussianState
import Definitions.Def_BosonicResources_IsGaussianMeasurement
import Definitions.Def_BosonicResources_IsPure
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open BosonicLearn

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BosonicResources

/-- **Theorem 5 (Nearly-optimal learning of pure Gaussian states).**
Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, *What resources are needed for optimal learning of bosonic
Gaussian states?*, arXiv:2603.18136, Theorem 5, Eq. (4): "A number of N = Õ(n²/ε²) = O(n²/ε² + (n + log log log Ē) log log Ē) copies are sufficient
to learn an n-mode Gaussian state ρ(µ,Σ) to ε trace distance closeness with probability 2/3 given the promise that ρ
is pure and ‖Σ‖_op ≤ Ē. Moreover, this can be achieved by Gaussian measurements." Precise form, Theorem S8 (App. D.1):
"There exists a protocol using adaptive general-dyne measurements …".

There is a universal `C > 0` such that for every `n ≥ 1`, `ε ∈ (0, 1)` and `Ē ≥ 16` there are
`N ≤ C (n²/ε² + (n + log log log Ē) log log Ē)`, an adaptive single-copy scheme on `N` copies all of whose measurements
are Gaussian (general-dyne) measurements, and a (possibly randomized) estimator, which learn every pure Gaussian state
with `‖Σ‖_op ≤ Ē` to trace distance `ε` with probability at least `2/3`.

**Formalization Note.** `O(·)` is one constant uniform in `n, ε, Ē`. The bound is stated for `Ē ≥ 16`, the range in
which `log log Ē` and `log log log Ē` are positive (`e^e < 16`); a class with smaller `Ē` is contained in the class
for `Ē = 16`. The protocol (scheme and estimator) is chosen before the state. `‖Σ‖_op ≤ Ē` is `Ē·I − Σ ⪰ 0`. The
running-time claim of Theorem S8 is not part of the statement. -/
theorem theorem_5 :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ E : ℝ, 16 ≤ E →
      ∃ N : ℕ, (N : ℝ) ≤ C * ((n : ℝ) ^ 2 / ε ^ 2 +
          ((n : ℝ) + Real.log (Real.log (Real.log E))) * Real.log (Real.log E)) ∧
        ∃ Sch : AdaptiveScheme n N (EuclideanSpace ℝ (Fin n ⊕ Fin n)), IsGaussianScheme Sch ∧
          ∃ est : Kernel (Fin N → EuclideanSpace ℝ (Fin n ⊕ Fin n)) (State (Occupation (Fin n))),
            IsMarkovKernel est ∧
            ∀ (ρ : State (Occupation (Fin n))) (μ : Fin n ⊕ Fin n → ℝ)
                (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
              IsPure ρ → IsGaussianState ρ μ S →
              (E • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) - S).PosSemidef →
              ENNReal.ofReal (2 / 3) ≤ successProb Sch est ρ.coefficients ε := by sorry

end BosonicResources

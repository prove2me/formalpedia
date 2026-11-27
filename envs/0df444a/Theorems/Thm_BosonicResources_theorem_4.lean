-- Prove2me | Theorems.Thm_BosonicResources_theorem_4
-- name    : BosonicResources.theorem_4
-- status  : Open
-- author  : @Senrui Chen
-- created : 2026-11-27T06:35:43.326742+00:00
-- url     : https://prove2.me/theorems/186af4b2-e9e1-43df-96c4-78c5d962d8c0
-- title:
--   Theorem 4: $\Omega(\bar E^2 n^3/\varepsilon^2)$ copies are necessary with heterodyne measurements
-- statement:
--   Throughout, $\rho(\mu,\Sigma)$ denotes the $n$-mode Gaussian state with mean $\mu\in\mathbb R^{2n}$ and covariance matrix $\Sigma$, a real $2n\times 2n$ matrix; quadratures are ordered $(x_1,\dots,x_n,p_1,\dots,p_n)$ and the vacuum has covariance $\tfrac12 I$. A *Gaussian (general-dyne) measurement with seed covariance $V$* is the POVM on one copy with outcomes $\xi\in\mathbb R^{2n}$ and elements $(2\pi)^{-n}\rho(\xi,V)\,d\xi$, the displaced copies of a Gaussian seed state with covariance $V$. *Heterodyne detection* is the Gaussian measurement with seed covariance $V=\tfrac12 I$.
--
--   A *heterodyne protocol on $N$ copies* measures each of the $N$ copies by heterodyne detection and applies a possibly randomized estimator that maps the $N$ outcomes to a density operator $\hat\rho$; it *learns $\rho$ to trace distance $\varepsilon$* if $D_{\mathrm{tr}}(\hat\rho,\rho)=\tfrac12\|\hat\rho-\rho\|_1\le\varepsilon$ with probability at least $2/3$ over the outcomes and the randomness of the estimator.
--
--   There are universal constants $c>0$ and $n_0\in\mathbb N$ such that the following holds for every $n\ge n_0$, every $\varepsilon\in(0,0.005)$, every $\bar E>1$ and every $N$. If some heterodyne protocol on $N$ copies learns to trace distance $\varepsilon$ every zero-mean $n$-mode Gaussian state $\rho(0,\Sigma)$ with $\|\Sigma\|_{\mathrm{op}}\le\bar E$, then
--
--   $$
--   N\ \ge\ c\,\frac{\bar E^{2}\,n^{3}}{\varepsilon^{2}} .
--   $$
--
--   The theorem matches the heterodyne upper bound $O(\bar E^{2}n^{3}/\varepsilon^{2})$ of [BMEM25], so heterodyne tomography of Gaussian states has sample complexity $\Theta(\bar E^{2}n^{3}/\varepsilon^{2})$. Its quadratic dependence on the energy is the reference point for the energy dependence of adaptive schemes and of the non-adaptive schemes of Theorem 7.
--
--   **Formalization Note** The protocol is a single-copy scheme (`BosonicLearn.AdaptiveScheme`) all of whose measurements are heterodyne, i.e. satisfy `IsGaussianMeasurement` with seed $\tfrac12 I$; such a scheme has no settings to adapt. The estimator is a Markov kernel from the $N$ outcomes to states and success is `BosonicLearn.successProb`. The constant $c$ and the threshold $n_0$ are uniform in $\bar E>1$. The ranges $\varepsilon<0.005$ and $\bar E>1$, and the restriction to zero-mean states, are those of the precise form, Theorem S7. $\|\Sigma\|_{\mathrm{op}}\le\bar E$ is encoded as positive semidefiniteness of $\bar E\cdot I-\Sigma$.
-- source:
--   Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, What resources are needed for optimal learning of bosonic Gaussian states?, https://arxiv.org/abs/2603.18136, Sec. 3.2, Theorem 4; App. C.3, Theorem S7

import Mathlib
import Definitions.Def_BosonicLearn_successProb
import Definitions.Def_BosonicLearn_IsGaussianState
import Definitions.Def_BosonicResources_IsGaussianMeasurement
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open BosonicLearn

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BosonicResources

/-- **Theorem 4 (Lower bound with heterodyne measurements).**
Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, *What resources are needed for optimal learning of bosonic
Gaussian states?*, arXiv:2603.18136, Theorem 4: "N = Ω(Ē²n³/ε²) copies are necessary to learn an n-mode Gaussian state ρ(µ,Σ) with the promise that
‖Σ‖_op ≤ Ē to ε trace distance closeness with probability 2/3 using heterodyne measurements." Precise form, Theorem S7
(App. C.3): "an unknown zero-mean n-mode Gaussian state ρ(0,Σ), with the promise that ‖Σ‖_op ≤ Ē for some Ē > 1, to
trace distance precision ε < 0.005 … using only heterodyne measurements".

There are `c > 0` and `n₀` such that for every `n ≥ n₀`, `ε ∈ (0, 0.005)`, `Ē > 1` and `N`: if `N` copies are each
measured by heterodyne detection (the Gaussian measurement with seed covariance `½I`, §2) and some, possibly
randomized, estimator of the `N` outcomes learns every zero-mean Gaussian state with `‖Σ‖_op ≤ Ē` to trace distance
`ε` with probability at least `2/3`, then `N ≥ c Ē² n³/ε²`.

**Formalization Note.** The protocol is a single-copy scheme all of whose measurements are heterodyne; such a scheme
has no settings to adapt. The constant `c` is uniform in `Ē > 1`. `‖Σ‖_op ≤ Ē` is `Ē·I − Σ ⪰ 0`. -/
theorem theorem_4 :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ ε : ℝ, 0 < ε → ε < 0.005 → ∀ E : ℝ, 1 < E →
      ∀ (N : ℕ) (Sch : AdaptiveScheme n N (EuclideanSpace ℝ (Fin n ⊕ Fin n)))
        (est : Kernel (Fin N → EuclideanSpace ℝ (Fin n ⊕ Fin n)) (State (Occupation (Fin n)))),
        IsMarkovKernel est →
        (∀ (t : Fin N) (x : Fin t → EuclideanSpace ℝ (Fin n ⊕ Fin n)),
          IsGaussianMeasurement (Sch.povm t x)
            ((1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ))) →
        (∀ (ρ : State (Occupation (Fin n))) (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
          IsGaussianState ρ 0 S →
          (E • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) - S).PosSemidef →
          ENNReal.ofReal (2 / 3) ≤ successProb Sch est ρ.coefficients ε) →
        c * (E ^ 2 * (n : ℝ) ^ 3 / ε ^ 2) ≤ N := by sorry

end BosonicResources

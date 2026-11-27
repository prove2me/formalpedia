-- Prove2me | Theorems.Thm_BosonicResources_theorem_1
-- name    : BosonicResources.theorem_1
-- status  : Open
-- author  : @Senrui Chen
-- created : 2026-11-27T06:30:29.879409+00:00
-- url     : https://prove2.me/theorems/e1d29863-d815-47a1-b987-af750cde36e0
-- title:
--   Theorem 1: nearly-optimal learning of Gaussian Wigner distributions
-- statement:
--   This theorem determines, up to doubly logarithmic terms in the energy, how many copies of a Gaussian state are needed to learn its Wigner distribution in total variation distance:
--
--   $$
--   N=\Omega\!\Big(\frac{n^{2}}{\varepsilon^{2}}\Big)\ \text{ is necessary,}\qquad N=O\!\Big(\frac{n^{2}}{\varepsilon^{2}}+\big(n+\log\log\log\bar E\big)\log\log\bar E\Big)\ \text{ is sufficient.}
--   $$
--
--   **Setting.** Throughout, $\rho(\mu,\Sigma)$ denotes the $n$-mode Gaussian state with mean $\mu\in\mathbb R^{2n}$ and covariance matrix $\Sigma$, a real $2n\times 2n$ matrix; quadratures are ordered $(x_1,\dots,x_n,p_1,\dots,p_n)$ and the vacuum has covariance $\tfrac12 I$. The Wigner distribution of $\rho(\mu,\Sigma)$ is $\mathcal N(\mu,\Sigma)$, the Gaussian probability measure on $\mathbb R^{2n}$ with mean $\mu$ and covariance $\Sigma$. For probability measures $P,Q$ on the same space, $\mathrm{TV}(P,Q)=\sup_A\lvert P(A)-Q(A)\rvert$ (supremum over measurable sets) is the total variation distance. A learner outputs a probability measure $\nu$ on $\mathbb R^{2n}$ and *succeeds on* $\rho(\mu,\Sigma)$ if $\mathrm{TV}(\nu,\mathcal N(\mu,\Sigma))\le\varepsilon$.
--
--   A *Gaussian (general-dyne) measurement with seed covariance $V$* is the POVM on one copy with outcomes $\xi\in\mathbb R^{2n}$ and elements $(2\pi)^{-n}\rho(\xi,V)\,d\xi$, the displaced copies of a Gaussian seed state with covariance $V$. An *adaptive single-copy scheme* measures the $N$ copies one at a time, and the POVM applied to the $t$-th copy may depend on the outcomes of the first $t-1$ measurements. Here $\log$ is the natural logarithm.
--
--   1. *(Necessity.)* There are universal constants $c>0$, $\varepsilon_0>0$, $E_0\in\mathbb R$ and $n_0\in\mathbb N$ such that for all $n\ge n_0$, all $\varepsilon\in(0,\varepsilon_0)$, all $N$ and every POVM on $N$ copies (possibly entangled across the copies) whose outcome is a probability measure $\nu$ on $\mathbb R^{2n}$: if for every $n$-mode Gaussian state $\rho(\mu,\Sigma)$ with $\|\Sigma\|_{\mathrm{op}}\le E_0$ the outcome of the POVM on $\rho^{\otimes N}$ succeeds with probability at least $2/3$, then $N\ge c\,n^{2}/\varepsilon^{2}$.
--   2. *(Sufficiency.)* There is a universal constant $C>0$ such that for all $n\ge1$, all $\varepsilon\in(0,1)$ and all $\bar E\ge16$ there exist an integer $N\le C\big(n^{2}/\varepsilon^{2}+(n+\log\log\log\bar E)\log\log\bar E\big)$, an adaptive single-copy scheme on $N$ copies all of whose measurements are Gaussian measurements, and a possibly randomized estimator mapping the $N$ outcomes to a probability measure $\nu$ on $\mathbb R^{2n}$, such that for every $n$-mode Gaussian state $\rho(\mu,\Sigma)$ with $\|\Sigma\|_{\mathrm{op}}\le\bar E$ the output succeeds with probability at least $2/3$.
--
--   The theorem is the warm-up result of the paper: learning the Wigner distribution from copies of the state has the same $n^{2}/\varepsilon^{2}$ scaling as learning a classical $2n$-dimensional Gaussian from samples, and Gaussian measurements achieve it. Learning the state in trace distance is a different and, for classical measurements, strictly harder task.
--
--   **Formalization Note** The learner may output any probability measure, not only a Gaussian one. $\mathrm{TV}(P,Q)=\sup_A\lvert P(A)-Q(A)\rvert$ over measurable sets is the published `MarkovChainCLT.tvDist`, which for probability measures equals the paper's $\tfrac12\int\lvert p-q\rvert$. Part 1 is stated on the sub-class $\|\Sigma\|_{\mathrm{op}}\le E_0$ (the ensemble of the proof, Eq. (S90), has bounded covariance), which implies the bound for all Gaussian states and for the promise $\|\Sigma\|_{\mathrm{op}}\le\bar E$ at every $\bar E\ge E_0$. Part 2 is stated for $\bar E\ge16$, where the iterated logarithms are positive. $\|\Sigma\|_{\mathrm{op}}\le E$ is encoded as positive semidefiniteness of $E\cdot I-\Sigma$. $\varepsilon_0$ is the "sufficiently small constant" of the proof (App. C.2.1). In part 2 the scheme is a `BosonicLearn.AdaptiveScheme` satisfying `IsGaussianScheme` (the seed covariance may depend on the round and on earlier outcomes) and the estimator is a Markov kernel from transcripts to probability measures.
-- source:
--   Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, What resources are needed for optimal learning of bosonic Gaussian states?, https://arxiv.org/abs/2603.18136, Sec. 3.1, Theorem 1; App. B.2, Theorem S2; Table 1

import Mathlib
import Definitions.Def_BosonicLearn_collectiveSuccess
import Definitions.Def_BosonicLearn_transcriptLaw
import Definitions.Def_BosonicLearn_IsGaussianState
import Definitions.Def_BosonicResources_IsGaussianMeasurement
import Definitions.Def_TotalVariationDist
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open BosonicLearn

open MeasureTheory ProbabilityTheory
open MarkovChainCLT (tvDist)
open scoped ENNReal Matrix

namespace BosonicResources

/-- **Theorem 1 (Nearly-optimal learning of Gaussian Wigner distributions).**
Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, *What resources are needed for optimal learning of bosonic
Gaussian states?*, arXiv:2603.18136, Theorem 1 (= Theorem S2, App. B.2): "N = Ω(n²/ε²) copies of an n-mode Gaussian state ρ(µ,Σ) are necessary to
learn its Wigner distribution to ε TV distance with probability 2/3 using any measurements. Furthermore, there exists
a Gaussian measurement scheme that achieves this using N = Õ(n²/ε²) = O(n²/ε² + (n + log log log Ē) log log Ē) copies
given the promise that ‖Σ‖_op ≤ Ē." Table 1: all bounds are "given the promise that ‖Σ‖_op ≤ Ē".

The Wigner distribution of the Gaussian state `ρ(µ, Σ)` is the Gaussian probability measure `N(µ, Σ)` on `ℝ²ⁿ` (§2).
1. (necessity) There are `c > 0`, `ε₀ > 0`, `E₀`, `n₀` such that for `n ≥ n₀`, `ε ∈ (0, ε₀)`, every `N` and every POVM
   on `N` copies (entangled across copies) whose outcome is a probability measure on `ℝ²ⁿ`: if for every Gaussian
   state with `‖Σ‖_op ≤ E₀` the output is within total variation distance `ε` of `N(µ, Σ)` with probability at least
   `2/3`, then `N ≥ c n²/ε²`.
2. (sufficiency) There is `C > 0` such that for `n ≥ 1`, `ε ∈ (0, 1)`, `Ē ≥ 16` there are
   `N ≤ C (n²/ε² + (n + log log log Ē) log log Ē)`, an adaptive single-copy scheme all of whose measurements are
   Gaussian measurements, and a (possibly randomized) estimator with values in probability measures on `ℝ²ⁿ`, whose
   output is within total variation distance `ε` of `N(µ, Σ)` with probability at least `2/3` for every Gaussian state
   with `‖Σ‖_op ≤ Ē`.

**Formalization Note.** The learner may output any probability measure, not only a Gaussian one. `TV(P, Q) = sup_A |P(A) − Q(A)|` over measurable sets (the published
`MarkovChainCLT.tvDist`), which for probability measures equals the paper's `½ ∫ |p − q|`. Part 1 is stated on
the sub-class `‖Σ‖_op ≤ E₀` (the ensemble of the proof, Eq. (S90), has bounded covariance), which implies the bound
for all Gaussian states and for the promise `‖Σ‖_op ≤ Ē` at every `Ē ≥ E₀`. Part 2 is stated for `Ē ≥ 16`, where
the iterated logarithms are positive. `‖Σ‖_op ≤ E` is `E·I − Σ ⪰ 0`. `ε₀` is the "sufficiently small constant" of
the proof (App. C.2.1). -/
theorem theorem_1 :
    (∃ c : ℝ, 0 < c ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ E₀ : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ (N : ℕ) (P : FockPOVM (Fin N → Occupation (Fin n))
          (ProbabilityMeasure (EuclideanSpace ℝ (Fin n ⊕ Fin n)))),
        (∀ (ρ : State (Occupation (Fin n))) (μ : Fin n ⊕ Fin n → ℝ)
            (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
          IsGaussianState ρ μ S →
          (E₀ • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) - S).PosSemidef →
          ENNReal.ofReal (2 / 3) ≤ P.law (WildeQIT.Schumacher.tensorPow N ρ.coefficients)
            {ν | tvDist (ν : Measure (EuclideanSpace ℝ (Fin n ⊕ Fin n)))
              (multivariateGaussian (WithLp.toLp 2 μ) S) ≤ ε}) →
        c * ((n : ℝ) ^ 2 / ε ^ 2) ≤ N) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ E : ℝ, 16 ≤ E →
      ∃ N : ℕ, (N : ℝ) ≤ C * ((n : ℝ) ^ 2 / ε ^ 2 +
          ((n : ℝ) + Real.log (Real.log (Real.log E))) * Real.log (Real.log E)) ∧
        ∃ Sch : AdaptiveScheme n N (EuclideanSpace ℝ (Fin n ⊕ Fin n)), IsGaussianScheme Sch ∧
          ∃ est : Kernel (Fin N → EuclideanSpace ℝ (Fin n ⊕ Fin n))
              (ProbabilityMeasure (EuclideanSpace ℝ (Fin n ⊕ Fin n))),
            IsMarkovKernel est ∧
            ∀ (ρ : State (Occupation (Fin n))) (μ : Fin n ⊕ Fin n → ℝ)
                (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
              IsGaussianState ρ μ S →
              (E • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) - S).PosSemidef →
              ENNReal.ofReal (2 / 3) ≤
                ∫⁻ x, est x {ν | tvDist (ν : Measure (EuclideanSpace ℝ (Fin n ⊕ Fin n)))
                  (multivariateGaussian (WithLp.toLp 2 μ) S) ≤ ε} ∂(transcriptLaw Sch ρ.coefficients)) := by sorry

end BosonicResources

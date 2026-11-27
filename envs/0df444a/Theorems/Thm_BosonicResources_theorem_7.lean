-- Prove2me | Theorems.Thm_BosonicResources_theorem_7
-- name    : BosonicResources.theorem_7
-- status  : Open
-- author  : @Senrui Chen
-- created : 2026-11-27T06:39:24.273783+00:00
-- url     : https://prove2.me/theorems/f99058f1-f05f-4408-9f33-c3aaecd73e7e
-- title:
--   Theorem 7: nearly tight $\widetilde\Theta(\bar E/\varepsilon^2)$ bound for non-adaptive single-copy Gaussian schemes (one mode)
-- statement:
--   The theorem concerns one-mode systems ($n=1$) and non-adaptive single-copy Gaussian measurements, for which the number of copies must grow linearly with the energy bound $\bar E$:
--
--   $$
--   N=\Omega\!\Big(\frac{\bar E}{\varepsilon^{2}}\Big)\ \text{ is necessary,}\qquad N=O\!\Big(\frac{\bar E\log\bar E}{\varepsilon^{2}}\Big)\ \text{ is sufficient.}
--   $$
--
--   **Setting.** For $\mu\in\mathbb R^{2}$ and a real $2\times2$ matrix $\Sigma$, $\rho(\mu,\Sigma)$ is the one-mode Gaussian state with mean $\mu$ and covariance $\Sigma$ (quadratures $(\hat x,\hat p)$, vacuum covariance $\tfrac12 I$). A Gaussian measurement with seed covariance $V$ is the POVM with outcomes $\xi\in\mathbb R^{2}$ and elements $(2\pi)^{-1}\rho(\xi,V)\,d\xi$.
--
--   A *non-adaptive single-copy Gaussian scheme* on $N$ copies consists of shared randomness $\omega$, drawn once from a probability measure on a measurable space $\Lambda$ independently of the state, and, for each $\omega$ and each copy $t$, a Gaussian measurement (with a seed covariance that may depend on $\omega$ and $t$) applied to copy $t$ alone; given $\omega$ the $N$ outcomes are independent, and no measurement depends on the outcome of another. An *estimator* is a possibly randomized map from $\omega$ and the $N$ outcomes to a density operator $\hat\rho$. The scheme and estimator *learn $\rho$ to trace distance $\varepsilon$* if $D_{\mathrm{tr}}(\hat\rho,\rho)=\tfrac12\|\hat\rho-\rho\|_1\le\varepsilon$ with probability at least $2/3$ over $\omega$, the outcomes and the randomness of the estimator. Here $\log$ is the natural logarithm.
--
--   1. *(Necessity.)* There are universal constants $c>0$, $\varepsilon_0>0$ and $E_0\in\mathbb R$ such that for every $\bar E\ge E_0$, every $\varepsilon\in(0,\varepsilon_0)$ and every $N$: if some non-adaptive single-copy Gaussian scheme on $N$ copies (with any space $\Lambda$ of shared randomness) and some estimator learn to trace distance $\varepsilon$ every zero-mean one-mode Gaussian state $\rho(0,\Sigma)$ with $\|\Sigma\|_{\mathrm{op}}\le\bar E$, then $N\ge c\,\bar E/\varepsilon^{2}$.
--   2. *(Sufficiency.)* There is a universal constant $C>0$ such that for every $\bar E\ge2$ and every $\varepsilon\in(0,1)$ there exist an integer $N\le C\,\bar E\log\bar E/\varepsilon^{2}$, a non-adaptive single-copy Gaussian scheme on $N$ copies and an estimator that learn to trace distance $\varepsilon$ every one-mode Gaussian state $\rho(\mu,\Sigma)$ with $\|\Sigma\|_{\mathrm{op}}\le\bar E$.
--
--   The adaptive single-copy Gaussian algorithm of [BMEM25] needs only $O(\varepsilon^{-2}+\log\log\bar E\,\log\log\log\bar E)$ copies in this setting, so the theorem shows that adaptivity is what makes the nearly energy-independent sample complexity possible. The non-adaptive scheme of part 2 also improves on heterodyne detection, which needs $\Theta(\bar E^{2}/\varepsilon^{2})$ copies (Theorem 4).
--
--   **Formalization Note** The main-text promise $\|\Sigma\|_{\mathrm{op}}\le\bar E$ is used in both parts, encoded as positive semidefiniteness of $\bar E\cdot I-\Sigma$; it implies the promises of Theorems S12 and S13 up to constants ($\operatorname{Tr}\Sigma\le2\bar E$, $\kappa(\Sigma)\le4\bar E^{2}$ because $\det\Sigma\ge1/4$), and it is implied by the promise of Theorem S12 with the same bound ($\operatorname{Tr}\Sigma\le\bar E$ gives $\|\Sigma\|_{\mathrm{op}}\le\bar E$). Part 1 is stated on zero-mean states as in Theorem S12, which is the stronger form. $\Omega$, $O$ are universal constants; part 1 has thresholds $\varepsilon_0$, $E_0$ (Theorem S12 has $\varepsilon\le0.04$, $E>2$), and part 2 assumes $\bar E\ge2$ so that $\log\bar E$ is bounded away from $0$. The scheme's own randomness (the random homodyne angles of Algorithm 1) is the shared randomness $\Lambda$; the estimator sees it. Schemes are `NonadaptiveGaussianScheme 1 N Λ`, the estimator is a Markov kernel on $\Lambda\times(\mathbb R^{2})^{N}$ and success is `nonadaptiveSuccess`; $\Lambda$ is universally quantified in part 1 and chosen by the protocol in part 2.
-- source:
--   Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, What resources are needed for optimal learning of bosonic Gaussian states?, https://arxiv.org/abs/2603.18136, Sec. 3.4, Theorem 7; App. E.1, Theorem S12; App. E.2, Theorem S13

import Mathlib
import Definitions.Def_BosonicLearn_IsGaussianState
import Definitions.Def_BosonicResources_NonadaptiveGaussianScheme
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open BosonicLearn

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BosonicResources

/-- **Theorem 7 (Adaptivity is necessary for energy-independent tomography via Gaussian schemes).**
Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, *What resources are needed for optimal learning of bosonic
Gaussian states?*, arXiv:2603.18136, Theorem 7: "Focus on one-mode systems and non-adaptive, non-entangling, Gaussian measurements. Then
N = Ω(Ē/ε²) copies are necessary to learn a Gaussian state ρ(µ,Σ) to ε trace distance closeness with probability 2/3
given the promise that ‖Σ‖_op ≤ Ē. Furthermore, there exists a scheme that achieves this using N = O(Ē log Ē/ε²)
samples." Precise forms: Theorem S12 (App. E.1; zero-mean states, "ε ≤ 0.04", "Tr Σ ≤ E for some E > 2") and
Theorem S13 (App. E.2; "κ(Σ) ≤ E² for some E > 2", `N = O(E log E/ε²)`).

For one mode (`n = 1`) and non-adaptive single-copy Gaussian measurement schemes (with shared randomness):
1. (necessity) there are `c > 0`, `ε₀ > 0` and `E₀` such that for every `Ē ≥ E₀`, `ε ∈ (0, ε₀)` and `N`, every such
   scheme on `N` copies with any (randomized) estimator that learns every zero-mean one-mode Gaussian state with
   `‖Σ‖_op ≤ Ē` to trace distance `ε` with probability at least `2/3` has `N ≥ c Ē/ε²`;
2. (sufficiency) there is `C > 0` such that for every `Ē ≥ 2` and `ε ∈ (0, 1)` some such scheme on
   `N ≤ C Ē log Ē/ε²` copies with some estimator learns every one-mode Gaussian state with `‖Σ‖_op ≤ Ē` to trace
   distance `ε` with probability at least `2/3`.

**Formalization Note.** The main-text promise `‖Σ‖_op ≤ Ē` is used in both parts (`Ē·I − Σ ⪰ 0`). It is comparable
with the promises of the appendix up to constants: `Tr Σ ≤ E` (Theorem S12) implies `‖Σ‖_op ≤ E`, so a learner for the
class of part 1 is a learner for the class of Theorem S12; and `‖Σ‖_op ≤ Ē` implies `κ(Σ) ≤ 4Ē²` (Theorem S13 with
`E = 2Ē`), because `det Σ ≥ 1/4`. Part 1 is stated
on zero-mean states as in Theorem S12, which is the stronger form. `Ω`, `O` are universal constants; thresholds
`ε₀`, `E₀` in part 1 (Theorem S12 has `ε ≤ 0.04`, `E > 2`), `Ē ≥ 2` in part 2 so that `log Ē` is bounded away from
`0`. The scheme's own randomness (the random homodyne angles of Algorithm 1) is the shared randomness `Λ`; the
estimator sees it. -/
theorem theorem_7 :
    (∃ c : ℝ, 0 < c ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ E₀ : ℝ, ∀ E : ℝ, E₀ ≤ E → ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ (N : ℕ) (Λ : Type) [MeasurableSpace Λ] (Sch : NonadaptiveGaussianScheme 1 N Λ)
        (est : Kernel (Λ × (Fin N → EuclideanSpace ℝ (Fin 1 ⊕ Fin 1))) (State (Occupation (Fin 1)))),
        IsMarkovKernel est →
        (∀ (ρ : State (Occupation (Fin 1))) (S : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ),
          IsGaussianState ρ 0 S →
          (E • (1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ) - S).PosSemidef →
          ENNReal.ofReal (2 / 3) ≤ nonadaptiveSuccess Sch est ρ.coefficients ε) →
        c * (E / ε ^ 2) ≤ N) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ E : ℝ, 2 ≤ E → ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ N : ℕ, (N : ℝ) ≤ C * (E * Real.log E / ε ^ 2) ∧
        ∃ (Λ : Type) (_ : MeasurableSpace Λ) (Sch : NonadaptiveGaussianScheme 1 N Λ)
          (est : Kernel (Λ × (Fin N → EuclideanSpace ℝ (Fin 1 ⊕ Fin 1))) (State (Occupation (Fin 1)))),
          IsMarkovKernel est ∧
          ∀ (ρ : State (Occupation (Fin 1))) (μ : Fin 1 ⊕ Fin 1 → ℝ)
              (S : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ),
            IsGaussianState ρ μ S →
            (E • (1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ) - S).PosSemidef →
            ENNReal.ofReal (2 / 3) ≤ nonadaptiveSuccess Sch est ρ.coefficients ε) := by sorry

end BosonicResources

-- Prove2me | Theorems.Thm_BanditAlgorithm_gaussian_baiComplexity_le_and_ne_top
-- name    : BanditAlgorithm.gaussian_baiComplexity_le_and_ne_top
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-31T19:41:43.297135+00:00
-- url     : https://prove2.me/theorems/3894af54-4f51-4bdd-99b3-fc57ba7236b7
-- title:
--   The characteristic time of a Gaussian bandit is finite, with an explicit gap bound
-- statement:
--   For a unit-variance Gaussian bandit with a unique best arm, the characteristic time is finite, $c^*(\nu)<\infty$, and it is bounded explicitly in terms of the smallest gap: if $\Delta>0$ satisfies $\Delta\le\mu_{i^*}-\mu_j$ for every $j\ne i^*$, then
--   $$c^*(\nu)\le\frac{4k}{\Delta^2}.$$
--
--   Finiteness is load-bearing rather than cosmetic. Theorem 33.6 asserts $\lim_{\delta\to0}\mathbb E[\tau_\delta]/\log(1/\delta)=c^*(\nu)$ through the real number $c^*(\nu)$, but $c^*(\nu)$ is defined in $[0,\infty]$, and the coercion $[0,\infty]\to\mathbb R$ sends $\infty$ to $0$; without finiteness the statement would silently degrade to a false claim. The bound comes from evaluating the defining supremum at the uniform allocation $\alpha_i=1/k$.
-- source:
--   Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), Eq. (33.4) and Section 33.2; Garivier & Kaufmann, COLT 2016, Section 3.

import Definitions.Def_TrackAndStop
import Definitions.Def_GaussianBandit

open MeasureTheory ProbabilityTheory InformationTheory NNReal ENNReal Filter

theorem BanditAlgorithm.gaussian_baiComplexity_le_and_ne_top {k : ℕ} [NeZero k]
    {μvec : Fin k → ℝ} {istar : Fin k}
    (hstar : ∀ j, j ≠ istar → μvec j < μvec istar) :
    BanditAlgorithm.baiComplexity (BanditAlgorithm.gaussianBandit μvec)
        (Set.range (BanditAlgorithm.gaussianBandit (k := k))) ≠ ⊤ ∧
      ∀ Δ : ℝ, 0 < Δ → (∀ j, j ≠ istar → Δ ≤ μvec istar - μvec j) →
        BanditAlgorithm.baiComplexity (BanditAlgorithm.gaussianBandit μvec)
            (Set.range (BanditAlgorithm.gaussianBandit (k := k)))
          ≤ ENNReal.ofReal (4 * (k : ℝ) / Δ ^ 2) := by
  sorry

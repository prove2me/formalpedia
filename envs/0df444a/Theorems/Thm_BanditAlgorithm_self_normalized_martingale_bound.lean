-- Prove2me | Theorems.Thm_BanditAlgorithm_self_normalized_martingale_bound
-- name    : BanditAlgorithm.self_normalized_martingale_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-29T00:16:40.557427+00:00
-- url     : https://prove2.me/theorems/fa14e704-c787-4bde-bdc0-91a937f3427e
-- statement:
--   (Self-normalized bound, method of mixtures, GOAL; L&S Theorem 20.4) With the setup above ($\mathcal{F}_t$-measurable actions $A_{t+1}$, $\mathcal{F}_{t+1}$-measurable conditionally 1-subgaussian noise $\eta_{t+1}$), let
--
--   $$S_t = \sum_{s=1}^t \eta_s A_s \quad\text{and}\quad V_t(\lambda) = \lambda I + \sum_{s=1}^t A_s A_s^\top.$$
--
--   Then for all $\lambda > 0$ and $\delta \in (0,1)$,
--
--   $$\mathbb{P}\left(\exists t \in \mathbb{N} : \|S_t\|^2_{V_t(\lambda)^{-1}} \ge 2\log\frac{1}{\delta} + \log\frac{\det V_t(\lambda)}{\lambda^d}\right) \le \delta,$$
--
--   uniformly over all times (the $\exists t$ is inside a single event).
-- source:
--   L&S Theorem 20.4, p.260

import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Martingale.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_SelfNormalizedProcess


open MeasureTheory ProbabilityTheory Matrix

theorem BanditAlgorithm.self_normalized_martingale_bound
    {Ω : Type} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} (ℱ : Filtration ℕ mΩ)
    (A : ℕ → Ω → Fin d → ℝ) (η : ℕ → Ω → ℝ)
    (hA : ∀ t : ℕ, Measurable[ℱ t] (A (t + 1)))
    (hη : ∀ t : ℕ, Measurable[ℱ (t + 1)] (η (t + 1)))
    (hsg : ∀ t : ℕ, HasCondSubgaussianMGF (ℱ t) (ℱ.le t) (η (t + 1)) 1 P)
    {lam : ℝ} (hlam : 0 < lam) {δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) :
    P.real {ω | ∃ t : ℕ,
        2 * Real.log (1 / δ)
            + Real.log ((regularizedDesignMatrix d lam A t ω).det / lam ^ d)
          ≤ selfNormalizedSum d η A t ω ⬝ᵥ
              (regularizedDesignMatrix d lam A t ω)⁻¹ *ᵥ
                selfNormalizedSum d η A t ω} ≤ δ := by
  sorry

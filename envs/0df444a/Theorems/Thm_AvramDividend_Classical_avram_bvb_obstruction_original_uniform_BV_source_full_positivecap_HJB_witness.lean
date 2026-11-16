-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_uniform_BV_source_full_positivecap_HJB_witness
-- name    : AvramDividend.Classical.avram_bvb_obstruction_original_uniform_BV_source_full_positivecap_HJB_witness
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T09:48:37.923199+00:00
-- url     : https://prove2.me/theorems/3dda2a98-8e32-43bd-a2b0-c0a7c2696a2f
-- title:
--   Genuine original standing BV uniform source simultaneously satisfies all positive-cap HJB and zero-barrier strategy hypotheses with positive-probability linear path
-- statement:
--   An explicit original Standing BV finite-activity negative-uniform Lévy law with unit drift and zero Gaussian component has a strictly positive nojump linear-path event through time one. The half-unit affine candidate, finite cap 1, discount rate 1 and genuine zero-barrier strategy satisfy every analytically specified HJB, regularity, gradient, admissibility, pre-ruin nonnegativity and right-dividend-jump hypothesis of the BV contact branch.
-- source:
--   Assemble Proved original source event, uniform coefficient c=1/2 from unit BV drift, full original positive-cap HJB candidate, true zero-barrier positive-cap admissibility, pre-ruin nonnegativity and exact right-jump budget.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_bvb_obstruction_original_uniform_BV_source_full_positivecap_HJB_witness :
    ∃ (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
      (𝓕 : Filtration ℝ≥0
        (inferInstance : MeasurableSpace ((ℕ → ℝ) × (ℕ → ℝ))))
      (X : SpectrallyNegativeLevy P 𝓕),
      X.Standing ∧ X.BoundedVariation ∧
      X.ν = (volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0) ∧
      X.ν (Iio (0 : ℝ)) < ⊤ ∧ X.drift = 1 ∧ X.σ = 0 ∧
      0 < P {ω |
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ (X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 (1 : ℝ≥0) ×ˢ Iio (0 : ℝ)) = 0 ∧
        (∀ t : ℝ≥0, t ≤ 1 → X.X t ω = (t : ℝ) * X.drift)} ∧
      (let w : ℝ → ℝ := fun y => if y < 0 then 0 else 1 / 2 + y
       let D := barrierStrategy X 0 0
       let C : ℝ≥0∞ := 1
       ContinuousOn w (Ici 0) ∧ 0 ≤ w 0 ∧
         (∀ z : ℝ, z < 0 → w z = 0) ∧
         ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} ∧
         (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
           X.GeneratorIntegrable w y ∧ X.generator w y - w y ≤ 0) ∧
         (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) ∧
         IsAdmissibleLe X 0 C D ∧
         (∀ ω (t : ℝ≥0), 0 < t →
           (t : ℝ≥0∞) < ruinTime X 0 D ω →
           0 ≤ w (riskProcess X 0 D t ω)) ∧
         (∀ ω (t : ℝ≥0),
           (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X 0 D ω) →
           rightLimit D t ω - D t ω ≤
             w (riskProcess X 0 D t ω) -
               w (riskProcess X 0 D t ω -
                 (rightLimit D t ω - D t ω)))) := by sorry

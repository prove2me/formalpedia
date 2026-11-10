-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin_source13_original_annulus_offtime_product_mean
-- name    : AvramDividend.Classical.avram_mix_fin_source13_original_annulus_offtime_product_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T07:27:25.513889+00:00
-- url     : https://prove2.me/theorems/e4a122b3-8ccf-48ca-802a-f139c7cf5a57
-- title:
--   Physical negative annulus off-time count product has exact Levy rate mean
-- statement:
--   For the actual original X.X negative annulus jump count on two disjoint ordered time windows (0,s] and (s,t], its real count product is integrable and has expectation equal to the product of its true original Levy compensator rates. Uses original same-band centred covariance 25c87c2d and original Borel first moment e3e7deac; this is the exact uncentred mesh product input for chronological original factorial pairs 6ea0212e, with no auxiliary point process.
-- source:
--   MIX-SOURCE-FIN13 physical annulus finite-grid factorial bridge

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mixed_source13_original_annulus_past_future_same_band_covariance_zero
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_separated_borel_cell_compensated_mean_zero_auto
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin_source13_original_annulus_offtime_product_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (n m : ℕ) (hnm : n ≤ m) :
    let B : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    let A : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 s ×ˢ B)
    let F : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)
    let r : ℝ := ((s : ℝ≥0∞) * X.ν B).toReal
    let q : ℝ := (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal
    Integrable (fun ω => (A ω).toReal * (F ω).toReal) P ∧
      (∫ ω, (A ω).toReal * (F ω).toReal ∂P) = r * q := by sorry

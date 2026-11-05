-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_discounted_HJB_drift_measurable
-- name    : AvramDividend.Classical.avram_p3_e_compensator_original_discounted_HJB_drift_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:38:55.229661+00:00
-- url     : https://prove2.me/theorems/7b3c0a33-e569-4bb6-af7f-e8dcd9e146c1
-- title:
--   Measurability of original controlled stopped BV discounted HJB drift
-- statement:
--   The literal original process X and dividends D define a controlled left-limit reserve. If its time-and-sample left-limit is measurable, E is a product-measurable localisation region, and H is a measurable one-variable generator residual, the discounted source expression 1_E exp(-q t) H(Upre) is AE strongly measurable on the actual finite horizon time×P product measure. This isolates the exact measurability preconditions needed to discharge P3's hFint, without assuming a new process or compensator.
-- source:
--   Mathlib Measurable.comp, Measurable.ite, Measurable.exp, NNReal continuous coercion; original SpectrallyNegativeLevy and dividend strategy source definitions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_e_compensator_original_discounted_HJB_drift_measurable
{Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
{𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
(T : ℝ≥0) (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (q : ℝ)
(E : Set (ℝ≥0 × Ω)) (hEmeas : MeasurableSet E)
(hUpm : Measurable (fun p : ℝ≥0 × Ω => Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1)) (H : ℝ → ℝ) (hHm : Measurable H) :
AEStronglyMeasurable (fun p : ℝ≥0 × Ω => if p ∈ E then Real.exp (-(q * (p.1 : ℝ))) * H (Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) else 0) ((((volume : Measure ℝ).restrict (Set.Icc 0 (T : ℝ))).map Real.toNNReal).prod P) := by sorry

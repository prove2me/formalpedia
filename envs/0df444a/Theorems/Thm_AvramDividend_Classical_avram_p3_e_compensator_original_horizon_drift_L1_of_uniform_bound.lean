-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_horizon_drift_L1_of_uniform_bound
-- name    : AvramDividend.Classical.avram_p3_e_compensator_original_horizon_drift_L1_of_uniform_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:15:40.149741+00:00
-- url     : https://prove2.me/theorems/00b5a3b3-9d4f-4210-8de5-526984e637d1
-- title:
--   Actual original bounded-horizon HJB drift is L1 under uniform domination and strong measurability
-- statement:
--   For the original SpectrallyNegativeLevy process X, any strongly measurable HJB drift integrand on the actual truncated Lebesgue-to-NNReal product time-probability measure is integrable when uniformly absolutely bounded. Finiteness of the source time-product follows from the actual X.isProbability and finite horizon, so there is no separate finite-mass assumption. This supplies a concrete sufficient criterion for hFint in the source stopped signed HJB compensation theorem.
-- source:
--   X.isProbability; Mathlib finite interval and product-measure instances; MeasureTheory.Integrable.of_bound. This is a sufficient criterion, not a claim of unconditional drift integrability. P3 must prove original F measurability and its uniform bound, with P3-G providing the predictable region.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_e_compensator_original_horizon_drift_L1_of_uniform_bound
{Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
{𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
(T : ℝ≥0) (F : ℝ≥0 × Ω → ℝ)
(hFm : AEStronglyMeasurable F ((((volume : Measure ℝ).restrict
  (Set.Icc 0 (T : ℝ))).map Real.toNNReal).prod P))
(C : ℝ) (hFbound : ∀ p : ℝ≥0 × Ω, |F p| ≤ C) :
Integrable F ((((volume : Measure ℝ).restrict
  (Set.Icc 0 (T : ℝ))).map Real.toNNReal).prod P) := by sorry

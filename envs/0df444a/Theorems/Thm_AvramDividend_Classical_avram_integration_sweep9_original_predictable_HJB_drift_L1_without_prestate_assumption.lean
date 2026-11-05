-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_integration_sweep9_original_predictable_HJB_drift_L1_without_prestate_assumption
-- name    : AvramDividend.Classical.avram_integration_sweep9_original_predictable_HJB_drift_L1_without_prestate_assumption
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T15:38:41.173235+00:00
-- url     : https://prove2.me/theorems/8e6b6290-6570-4e5a-a206-2f953c51e3ba
-- title:
--   Genuine original stopped HJB drift L1 with automatic prestate measurability
-- statement:
--   For the original spectrally-negative Levy X and an actual dividend strategy D, any right-continuous predictable interior region E, measurable H continuous on its compact physical reserve band and nonnegative discount yield the literal original stopped finite-horizon HJB drift integrable in the genuine time×P measure. The source strongly predictable prestate is automatically ambient measurable; no extra hUpm assumption is needed.
-- source:
--   Direct accepted import of original full-time prestate ambient measurable 63da8b2d and source-exact Proved P3-E HJB drift L1 6f1e0ef2, eliminating only its independent hUpm binder. This supplies original integrable hFint for P3-E stopped signed HJB under genuine other H/E hypotheses.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_integration_sweep9_original_controlled_prestate_ambient_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_predictable_continuous_HJB_drift_L1
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_integration_sweep9_original_predictable_HJB_drift_L1_without_prestate_assumption
{Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
{𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
(T : ℝ≥0) (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
(hD : IsDividendStrategy 𝓕 D) (q : ℝ) (hq : 0 ≤ q)
(E : Set (ℝ≥0 × Ω)) (hEm : MeasurableSet[𝓕.rightCont.predictable] E)
(a b : ℝ) (hab : a ≤ b)
(hEregion : ∀ p ∈ E, Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1 ∈ Set.Icc a b)
(H : ℝ → ℝ) (hHm : Measurable H)
(hHcont : ContinuousOn H (Set.Icc a b)) :
Integrable (fun p : ℝ≥0 × Ω => if p ∈ E then Real.exp (-(q * (p.1 : ℝ))) * H (Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) else 0) ((((volume : Measure ℝ).restrict (Set.Icc 0 (T : ℝ))).map Real.toNNReal).prod P) := by sorry

-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_local_continuous_HJB_drift_L1
-- name    : AvramDividend.Classical.avram_p3_e_compensator_original_local_continuous_HJB_drift_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:26:59.762205+00:00
-- url     : https://prove2.me/theorems/90a33677-5a36-4abf-b075-275d6b1ce385
-- title:
--   Original stopped HJB drift L1 from compact continuity without global H measurability
-- statement:
--   On the literal original stopped reserve, if the HJB residual is continuous on the compact prestate band and the original prestate is measurable, construct a globally continuous clamped extension of H. Its values agree with H on the genuine predictable interior region, so the existing source finite-horizon drift L1 theorem applies without globally measurable H as a hypothesis.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_predictable_continuous_HJB_drift_L1
open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_e_compensator_original_local_continuous_HJB_drift_L1
{Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
{𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
(T : ℝ≥0) (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (q : ℝ) (hq : 0 ≤ q)
(E : Set (ℝ≥0 × Ω)) (hEm : MeasurableSet[𝓕.rightCont.predictable] E)
(hUpm : Measurable (fun p : ℝ≥0 × Ω => Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1))
(a b : ℝ) (hab : a ≤ b)
(hEregion : ∀ p ∈ E, Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1 ∈ Set.Icc a b)
(H : ℝ → ℝ) (hHcont : ContinuousOn H (Set.Icc a b)) :
Integrable (fun p : ℝ≥0 × Ω => if p ∈ E then Real.exp (-(q * (p.1 : ℝ))) * H (Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) else 0) ((((volume : Measure ℝ).restrict (Set.Icc 0 (T : ℝ))).map Real.toNNReal).prod P) := by sorry

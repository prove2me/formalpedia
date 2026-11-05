-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_predictable_continuous_HJB_drift_L1
-- name    : AvramDividend.Classical.avram_p3_e_compensator_original_predictable_continuous_HJB_drift_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:47:35.499185+00:00
-- url     : https://prove2.me/theorems/6f1e0ef2-126d-4dd2-b1ca-b91a690cf3fa
-- title:
--   Automatic finite-horizon original HJB drift L1 from predictable interior and continuous generator
-- statement:
--   For original X,D and the true right-continuous predictable interior E, measurable controlled-reserve left limits plus a measurable generator residual H continuous on the compact local reserve band imply the exact finite-horizon original discounted drift is integrable. Derives ambient measurability of E, AE strong measurability of drift, finite local bound and product-time L1 via four independently Proved original-source helpers.
-- source:
--   Composition of P3-E predictable ambient, original discounted drift measurable, compact continuous generator bound and original HJB drift L1 of compact bound. Requires all four helpers to be Proved before publication.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_rightCont_predictable_ambient_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_discounted_HJB_drift_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_HJB_generator_compact_bound_of_continuity
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_HJB_drift_L1_of_compact_bound
open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_e_compensator_original_predictable_continuous_HJB_drift_L1
{Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
{𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
(T : ℝ≥0) (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (q : ℝ) (hq : 0 ≤ q)
(E : Set (ℝ≥0 × Ω)) (hEm : MeasurableSet[𝓕.rightCont.predictable] E)
(hUpm : Measurable (fun p : ℝ≥0 × Ω => Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1))
(a b : ℝ) (hab : a ≤ b)
(hEregion : ∀ p ∈ E, Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1 ∈ Set.Icc a b)
(H : ℝ → ℝ) (hHm : Measurable H)
(hHcont : ContinuousOn H (Set.Icc a b)) :
Integrable (fun p : ℝ≥0 × Ω => if p ∈ E then Real.exp (-(q * (p.1 : ℝ))) * H (Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) else 0) ((((volume : Measure ℝ).restrict (Set.Icc 0 (T : ℝ))).map Real.toNNReal).prod P) := by sorry

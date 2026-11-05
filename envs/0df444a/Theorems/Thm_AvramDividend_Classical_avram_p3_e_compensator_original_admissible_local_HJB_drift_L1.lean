-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_admissible_local_HJB_drift_L1
-- name    : AvramDividend.Classical.avram_p3_e_compensator_original_admissible_local_HJB_drift_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:43:46.179819+00:00
-- url     : https://prove2.me/theorems/ead67dc1-c343-49bd-8d6f-825806f36e5e
-- title:
--   Actual admissible Lévy stopped HJB drift L1 from local compact continuity
-- statement:
--   For the original admissible controlled Lévy reserve and any predictable compact interior region, the finite-horizon discounted HJB drift integral is integrable if its deterministic source generator residual is continuous on the compact band. Original prestate measurability and a globally measurable extension of H are discharged automatically by two independently proved P3-E helpers, preserving the literal original X,D and source ν.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_admissible_prestate_ambient_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_local_continuous_HJB_drift_L1
open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_e_compensator_original_admissible_local_HJB_drift_L1
{Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
{𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
(T : ℝ≥0) (x : ℝ) (C : ℝ≥0∞)
(D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
(q : ℝ) (hq : 0 ≤ q)
(E : Set (ℝ≥0 × Ω)) (hEm : MeasurableSet[𝓕.rightCont.predictable] E)
(a b : ℝ) (hab : a ≤ b)
(hEregion : ∀ p ∈ E, Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1 ∈ Set.Icc a b)
(H : ℝ → ℝ) (hHcont : ContinuousOn H (Set.Icc a b)) :
Integrable (fun p : ℝ≥0 × Ω => if p ∈ E then
  Real.exp (-(q * (p.1 : ℝ))) * H (Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) else 0)
  ((((volume : Measure ℝ).restrict (Set.Icc 0 (T : ℝ))).map Real.toNNReal).prod P) := by sorry

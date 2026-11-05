-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_BV_admissible_HJB_drift_L1_from_source
-- name    : AvramDividend.Classical.avram_p3_e_compensator_original_BV_admissible_HJB_drift_L1_from_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T17:07:52.951224+00:00
-- url     : https://prove2.me/theorems/4d383fd5-7b8c-4854-b220-4533406c43ef
-- title:
--   Complete original BV admissible stopped HJB drift L1 from source Lévy triplet
-- statement:
--   For an actual admissible original BV spectrally negative Lévy process and compact predictable reserve interior, derive integrability of the exact source stopped discounted HJB drift without assuming H globally measurable or continuous. The original Lévy source is sigma-finite, the ruin-extended value is measurable across zero, its derivative is measurable, and the true ν jump generator is measurable. The previously proved original uniform BV Lévy mark bound then gives a single L1 bound from a finite derivative bound and compact value/Lipschitz estimates. Exactly matches the hFint premise in P3-E's signed stopped HJB theorem.

import Mathlib
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_admissible_prestate_ambient_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_ruin_extension_value_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_levy_negative_mark_sigmaFinite
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_negative_jump_generator_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_BV_compact_HJB_drift_uniform
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_rightCont_predictable_ambient_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_discounted_HJB_drift_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_HJB_drift_L1_of_compact_bound
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_e_compensator_original_BV_admissible_HJB_drift_L1_from_source
{Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
{𝓕 : Filtration ℝ≥0 mΩ}
(X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
(T : ℝ≥0) (x : ℝ) (C : ℝ≥0∞)
(D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
(w : ℝ → ℝ) (hw_cont : ContinuousOn w (Set.Ici 0))
(hw_neg : ∀ y < 0, w y = 0)
(q : ℝ) (hq : 0 ≤ q)
(a b L R A : ℝ) (ha : 0 < a) (ha2 : a ≤ 2)
(hab : a ≤ b) (hL : 0 ≤ L) (hR : 0 ≤ R) (hA : 0 ≤ A)
(hLip : ∀ u ∈ Set.Icc (a / 2) b, ∀ v ∈ Set.Icc (a / 2) b,
  |w u - w v| ≤ L * |u - v|)
(hWbound : ∀ v : ℝ, v ≤ b → |w v| ≤ R)
(hDeriv : ∀ y ∈ Set.Icc a b, |deriv w y| ≤ A)
(E : Set (ℝ≥0 × Ω)) (hEm : MeasurableSet[𝓕.rightCont.predictable] E)
(hEregion : ∀ p ∈ E, Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1 ∈ Set.Icc a b) :
Integrable (fun p : ℝ≥0 × Ω => if p ∈ E then Real.exp (-(q * (p.1 : ℝ))) *
    (X.drift * deriv w (Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) +
     (∫ z in Set.Iio (0 : ℝ),
        w ((Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) + z) - w (Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) ∂X.ν) -
     q * w (Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1)) else 0)
  ((((volume : Measure ℝ).restrict (Set.Icc 0 (T : ℝ))).map Real.toNNReal).prod P) := by sorry

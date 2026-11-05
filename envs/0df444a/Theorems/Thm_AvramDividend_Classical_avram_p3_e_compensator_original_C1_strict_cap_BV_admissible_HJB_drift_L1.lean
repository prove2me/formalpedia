-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_C1_strict_cap_BV_admissible_HJB_drift_L1
-- name    : AvramDividend.Classical.avram_p3_e_compensator_original_C1_strict_cap_BV_admissible_HJB_drift_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T17:23:18.156694+00:00
-- url     : https://prove2.me/theorems/8e8145d0-f7c2-4ffe-a32a-a0213bcbabb5
-- title:
--   Original admissible stopped BV HJB drift L1 directly from canonical strict-cap C1
-- statement:
--   For literal original BV X,D and the original predictable compact cap-safe reserve interior, discharge the exact P3 signed stopped-compensation hFint automatically from canonical C1 smoothness on the strict cap region, without separate Lipschitz constant, global value bound, derivative bound, H-continuity, or assumed Levy compensator.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_strict_cap_C1_Lipschitz
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_negative_jump_halfline_bound_of_continuity
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_strict_cap_C1_derivative_compact_bound
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_BV_admissible_HJB_drift_L1_from_source
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_e_compensator_original_C1_strict_cap_BV_admissible_HJB_drift_L1
{Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
{𝓕 : Filtration ℝ≥0 mΩ}
(X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
(T : ℝ≥0) (x : ℝ) (C : ℝ≥0∞)
(D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
(w : ℝ → ℝ) (hw_cont : ContinuousOn w (Set.Ici 0))
(hw_neg : ∀ y < 0, w y = 0)
(q : ℝ) (hq : 0 ≤ q)
(a b : ℝ) (ha : 0 < a) (ha2 : a ≤ 2)
(hab : a ≤ b) (hbC : ENNReal.ofReal b < C)
(hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
(E : Set (ℝ≥0 × Ω)) (hEm : MeasurableSet[𝓕.rightCont.predictable] E)
(hEregion : ∀ p ∈ E, Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1 ∈ Set.Icc a b) :
Integrable (fun p : ℝ≥0 × Ω => if p ∈ E then Real.exp (-(q * (p.1 : ℝ))) *
    (X.drift * deriv w (Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) +
     (∫ z in Set.Iio (0 : ℝ),
        w ((Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) + z) - w (Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) ∂X.ν) -
     q * w (Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1)) else 0)
  ((((volume : Measure ℝ).restrict (Set.Icc 0 (T : ℝ))).map Real.toNNReal).prod P) := by sorry

-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_simultaneous_source_dividend_jump_without_hjump
-- name    : AvramDividend.Classical.avram_wave7_02_original_BV_simultaneous_source_dividend_jump_without_hjump
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:24:01.254374+00:00
-- url     : https://prove2.me/theorems/f0395815-4f78-4e13-b634-4351cabb77cf
-- title:
--   Original BV controlled simultaneous negative source jump and dividend HJB correction with automatic C1 hjump
-- statement:
--   For the genuine original bounded variation Lévy-controlled reserve, after a simultaneous negative source jump and right dividend atom, the combined HJB correction is nonpositive using solely C1 gradient, original admissibility, and cap data. The canonical hjump input is obtained from a proved source-specific theorem rather than assumed independently. Original X, riskProcess, rightLimit D and filtration are preserved.
-- source:
--   Compose Proved original simultaneous source/right-dividend correction with proved canonical hjump-from-admissibility on identical source and parameters.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_canonical_hjump_of_C1_and_admissible
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_simultaneous_source_then_dividend_full_HJB_jump_nonpos
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_BV_simultaneous_source_dividend_jump_without_hjump
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0)
    (ht : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω)
    (hMark : X.X t ω ≤
      Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)
    (hb : 0 ≤ x +
      Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω)
    (hbC : ENNReal.ofReal (x +
      Function.leftLim (fun s : ℝ≥0 => X.X s ω) t -
        D t ω) ≤ C) :
    (rightLimit D t ω - D t ω) +
      w (riskProcess X x D t ω -
        (rightLimit D t ω - D t ω)) -
      w (x + Function.leftLim
        (fun s : ℝ≥0 => X.X s ω) t - D t ω) ≤ 0 := by sorry

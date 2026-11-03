-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_corrected_boundary_hjb_pre_ruin_terminal_nonneg
-- name    : AvramDividend.Classical.avram_wave6_08_original_corrected_boundary_hjb_pre_ruin_terminal_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T10:21:38.828583+00:00
-- url     : https://prove2.me/theorems/818f0ea3-3ab3-41ac-b4cd-fb5e35ab76aa
-- title:
--   Corrected boundary and HJB gradient give nonnegative original capped verification terminal throughout pre-ruin time
-- statement:
--   For the actual original spectrally negative Lévy process with admissible positive-cap dividends, including cap infinity, nonnegative w(0), continuous w on nonnegative reserves, and interior HJB gradient w'≥1, the original pre-ruin controlled reserve lies in [0,C]. The already Proved full endpoint-inclusive secant gives reserve≤w(reserve)-w(0), hence w(reserve)≥0 at all strictly pre-ruin times including t=0. No stochastic Itô or martingale estimate is assumed. This directly supplies the corrected verification terminal sign.
-- source:
--   Proved original capped reserve range, admissible x≥0 and the endpoint-inclusive HJB secant; real linear arithmetic.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_allCap_admissible_initial_capital_nonneg
import Theorems.Thm_AvramDividend_Classical_capped_riskProcess_range_before_ruin_including_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_08_original_corrected_boundary_hjb_pre_ruin_terminal_nonneg
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y) :
    ∀ (ω : Ω) (t : ℝ≥0),
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω) := by sorry

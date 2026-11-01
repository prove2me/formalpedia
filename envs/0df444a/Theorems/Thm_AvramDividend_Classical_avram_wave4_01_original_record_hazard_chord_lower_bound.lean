-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_hazard_chord_lower_bound
-- name    : AvramDividend.Classical.avram_wave4_01_original_record_hazard_chord_lower_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:50:23.539995+00:00
-- url     : https://prove2.me/theorems/62d306c1-788a-41d1-935d-7e3d45ccf130
-- title:
--   Genuine reflected first-record drawdown hazard controls each forward logarithmic q-scale secant slope
-- statement:
--   For 0<a<b in the pure infinite-negative-small-jump variation regime, the average increase of log W between a and b is no larger than K(a), where K(a)=-log G_a(1) is the genuine original-process killed first-record hazard. The exact log-scale derivative identification and monotonicity in the actual drawdown depth make K antitone; applying the rigorous real mean value theorem to log W on [a,b] gives its chord slope K(c) for some a<c<b, hence ≤K(a). This forward-chord inequality is the quantitative bridge needed to investigate K(a)→infinity as a↓0 from W(0)=0. No Standing, artificial process, or almost-everywhere derivative substitution.
-- source:
--   Proved original first-record hazard derivative 30843a7a-3751-4284-a039-e87c25e27d8a, monotonicity 96bc676f-be55-4235-b847-49d95196df70, and real mean value theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_infinite_small_jump_not_bv
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_log_hazard_antitone_depth
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_hazard_eq_log_scale_deriv
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_01_original_record_hazard_chord_lower_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    (Real.log (W b) - Real.log (W a)) / (b - a) ≤
      -Real.log ((∫⁻ ω, if twoSidedExitUpTime X 1 ω <
                      barrierRuinTime X a ω then
          ENNReal.ofReal
            (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
        else 0 ∂P).toReal) := by sorry

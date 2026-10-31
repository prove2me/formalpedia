-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_01_original_record_factor_tendsto_one_zero
-- name    : AvramDividend.Classical.avram_wave3_01_original_record_factor_tendsto_one_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-10-30T22:07:40.07199+00:00
-- url     : https://prove2.me/theorems/acc124cd-0ace-4124-8d89-7cc8fbe951a6
-- title:
--   Genuine reflected first-record factor tends to unity at zero record height
-- statement:
--   For the original spectrally negative Lévy process with infinite small-jump variation and genuine reflected ruin, the expected discounted first upward record before ruin tends to one as its record height decreases to zero through positive reals. The proof is a two-sided squeeze by the already accepted Standing-free q-scale ratios W(a-h)/W(a) and W(a)/W(a+h), using positivity and continuity of W at every a>0.
-- source:
--   Accepted corrected two-sided exit and original-record sandwich; scaleFunction_continuousAt_away_zero and infinite-jump-to-unbounded-variation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_scaleFunction_continuousAt_away_zero
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_infinite_small_jump_not_bv
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_unbounded_genuine_record_scale_sandwich
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_01_original_record_factor_tendsto_one_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (hjump : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤)
    (a : ℝ) (ha : 0 < a) :
    Tendsto (fun h : ℝ =>
      ∫⁻ ω, if twoSidedExitUpTime X h ω < barrierRuinTime X a ω then
        ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
      else 0 ∂P) (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ≥0∞)) := by sorry

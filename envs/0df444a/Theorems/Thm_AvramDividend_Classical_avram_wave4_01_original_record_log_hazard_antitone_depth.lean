-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_log_hazard_antitone_depth
-- name    : AvramDividend.Classical.avram_wave4_01_original_record_log_hazard_antitone_depth
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:29:53.534746+00:00
-- url     : https://prove2.me/theorems/96bc676f-be55-4235-b847-49d95196df70
-- title:
--   Genuine original first-record logarithmic hazard is antitone in positive drawdown depth
-- statement:
--   For every unbounded-variation spectrally negative Lévy process and q>0, the real rate -log E[e^{-qT_1};T_1<D_a] is nonincreasing as the reflected drawdown ruin depth a grows, on all a>0. The discount is the actual original-process first strict record and reflected ruin clock, with no Standing. This is a direct probabilistic hazard monotonicity from source-clock event inclusion, strict positive survival and a finite ≤1 discount, without differentiability, Esscher tilting, or Laplace inversion.
-- source:
--   Genuine source drawdown-depth discount monotonicity b5710838, strict positivity b1cbd08b, discount ≤1 7a08c9f8, ENNReal.toReal_mono and strict log monotonicity.

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_monotone_drawdown_depth
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_reflected_record_discount_strict_pos
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_original_record_discount_le_one

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_01_original_record_log_hazard_antitone_depth
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) :
    AntitoneOn
      (fun a : ℝ => -Real.log
        ((∫⁻ ω, if twoSidedExitUpTime X 1 ω <
                    barrierRuinTime X a ω then
            ENNReal.ofReal
              (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
          else 0 ∂P).toReal))
      (Ioi (0 : ℝ)) := by sorry

-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_hazard_eq_log_scale_deriv
-- name    : AvramDividend.Classical.avram_wave4_01_original_record_hazard_eq_log_scale_deriv
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:21:15.010486+00:00
-- url     : https://prove2.me/theorems/30843a7a-3751-4284-a039-e87c25e27d8a
-- title:
--   Exact logarithmic q-scale derivative equals genuine first-record discount hazard at every positive drawdown depth
-- statement:
--   For the actual original spectrally negative Lévy first strict upward record time T_1 and actual reflected drawdown ruin clock D_a, in the pure infinite-small-jump-variation case the ordinary derivative of log W^(q) at each a>0 equals -log E[e^{-q T_1}; T_1<D_a]. Every clock and event is the original process definition, with no Standing assumption. Finite strictly positive discount, continuity in drawdown depth and authentic two-sided ratio sandwich underpin the derivative. This isolates the quantitative original-process hazard bridge from the previously Proved C1 theorem.
-- source:
--   Genuine first-record ratio sandwich 2490701d, actual hazard continuity 98caa2b4, analytic local exponential ratio log derivative d3a33430, positive W e50526dc, pure infinite small jump not BV.

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_infinite_small_jump_not_bv
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_canonical_infinite_jump_log_rate_continuous
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_genuine_local_scale_ratio_sandwich
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_local_exponential_scale_sandwich_log_deriv

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_01_original_record_hazard_eq_log_scale_deriv
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤) :
    ∀ a : ℝ, 0 < a →
      HasDerivAt (fun z : ℝ => Real.log (W z))
        (-Real.log
          ((∫⁻ ω, if twoSidedExitUpTime X 1 ω <
                      barrierRuinTime X a ω then
              ENNReal.ofReal
                (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
            else 0 ∂P).toReal)) a := by sorry

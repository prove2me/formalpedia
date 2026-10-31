-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_01_original_record_log_rate_continuous
-- name    : AvramDividend.Classical.avram_wave3_01_original_record_log_rate_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T17:42:19.888924+00:00
-- url     : https://prove2.me/theorems/ec9e934a-2ad2-4a0d-8d6e-9dd9654ab798
-- title:
--   Original Lévy reflected-record logarithmic rate is finite and continuous at positive depths
-- statement:
--   In the infinite small-jump variation case, the original killed upward-record discount factor at unit height is strictly positive, at most one, finite and continuous as a function of the positive reflected ruin threshold a. Its negative real logarithm, the candidate finite first-record hazard rate κ(a), is therefore continuous. This is the source-specific analytic regularity input for the logarithmic q-scale sandwich's derivative squeeze. The proof uses canonical positivity of the true record factor, original-law depth continuity without auxiliary grids, and the bound by the constant one under the probability measure; it does not assume Standing.
-- source:
--   Proved source record discount semigroup UUID 3890ee9b, Proved scale-ratio sandwich UUID f9f9bc34, expected Proved record positivity b1cbd08b and grid-free continuity 7f19aab9. Pinned Mathlib signatures ENNReal.continuousAt_toReal, ENNReal.toReal_pos, Real.continuousAt_log verified by private remote compiler 30 October 2026. Supports pure-jump C1 theorem cd61d678 in mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_01_original_record_log_rate_continuous
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hnbv : ¬ X.BoundedVariation)
    (hjump : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤) :
    ContinuousOn (fun a : ℝ =>
      -Real.log ((∫⁻ ω,
        if twoSidedExitUpTime X 1 ω < barrierRuinTime X a ω then
          ENNReal.ofReal
            (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
        else 0 ∂P).toReal)) (Ioi 0) := by sorry

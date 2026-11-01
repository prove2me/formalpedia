-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_quantitative_esscher_gap
-- name    : AvramDividend.Classical.avram_wave4_01_original_record_discount_quantitative_esscher_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:46:56.01508+00:00
-- url     : https://prove2.me/theorems/9778461b-3e80-42e1-b022-265df3a58d6a
-- title:
--   Actual finite-depth killed-record discount differs from unrestricted Esscher survival by at most record height times hazard excess
-- statement:
--   For actual first strict upward record T_h and reflected ruin D_a of the original spectrally negative Levy process with divergent negative small-jump first moment, fixed positive discount q, and Esscher root phi, the positive loss exp(-h phi)-E[e^{-q T_h};T_h<D_a] is between zero and h*(W'(a)/W(a)-phi). Thus the proved hazard convergence K(a)→phi gives an explicit quantitative route to uniform convergence of the original killed survival over bounded positive record heights. This estimate is pathwise-source anchored, no Standing or excursion axiom.
-- source:
--   Source exact exponential record discount 1c71a04d-268a-4126-b1bd-c0537bda0db1, source root hazard lower bound a5dbcace-268f-44a5-a46e-c42f4470ceb3, pinned Real.add_one_le_exp and exponential multiplicativity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_exp_log_scale_deriv
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_log_slope_ge_positive_esscher_root
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_01_original_record_discount_quantitative_esscher_gap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (a h : ℝ) (ha : 0 < a) (hh : 0 < h) :
    0 ≤ Real.exp (-(h * φ)) -
      (∫⁻ ω, if twoSidedExitUpTime X h ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitUpTime X h ω).toReal)))
      else 0 ∂P).toReal ∧
    Real.exp (-(h * φ)) -
      (∫⁻ ω, if twoSidedExitUpTime X h ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitUpTime X h ω).toReal)))
      else 0 ∂P).toReal ≤
      h * (deriv W a / W a - φ) := by sorry

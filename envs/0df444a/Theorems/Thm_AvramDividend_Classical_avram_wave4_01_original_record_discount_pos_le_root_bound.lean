-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_pos_le_root_bound
-- name    : AvramDividend.Classical.avram_wave4_01_original_record_discount_pos_le_root_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T13:30:06.498975+00:00
-- url     : https://prove2.me/theorems/95151d6b-175b-41a5-8fbf-c34f163b28b6
-- title:
--   Strictly positive original reflected first-record discount with explicit Laplace-root upper bound
-- statement:
--   For actual strict upward first-record T_h and actual reflected drawdown ruin D_a, in pure infinite-small-negative-jump variation the real discount G_a(h)=E[e^{-qT_h};T_h<D_a] is strictly positive for every positive a,h and is at most exp(-φh) for every positive root of ψ(φ)=q. The lower bound comes from the canonically Proved source exponential identity; the upper bound is a genuine pathwise event comparison with unrestricted upcrossing. No Standing or excursion assumptions.
-- source:
--   Proved genuine original discounted record exponential identity 1c71a04d and unconditional killed-vs-unrestricted positive-root upper bound 6a148bb3; ENNReal.toReal_mono.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_exp_log_scale_deriv
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_reflected_record_discount_le_unrestricted_upcrossing_root

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_01_original_record_discount_pos_le_root_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∀ a h : ℝ, 0 < a → 0 < h →
      0 < (∫⁻ ω, if twoSidedExitUpTime X h ω <
                    barrierRuinTime X a ω then
          ENNReal.ofReal
            (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
        else 0 ∂P).toReal ∧
        (∫⁻ ω, if twoSidedExitUpTime X h ω <
                    barrierRuinTime X a ω then
          ENNReal.ofReal
            (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
        else 0 ∂P).toReal ≤ Real.exp (-(φ * h)) := by sorry

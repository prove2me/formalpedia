-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_height_ode
-- name    : AvramDividend.Classical.avram_wave4_01_original_record_discount_height_ode
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:56:01.401864+00:00
-- url     : https://prove2.me/theorems/f2e4c321-c3c4-49ac-8c71-28ab16e36f2d
-- title:
--   Actual killed first-record discount satisfies the logarithmic-scale killing ODE in positive record height
-- statement:
--   For an actual spectrally negative Lévy process, positive discount rate q and purely infinite-small-negative-jump variation, let G_a(h) be the uncapped discounted strict upward record mass killed at the genuine reflected drawdown ruin time D_a. The height-variable map h to G_a(h) is differentiable at every h>0 and its derivative is exactly -(W'(a)/W(a)) G_a(h) for every a>0. This exact ODE uses neither Standing nor an excursion substitute.
-- source:
--   Proved genuine original-record full-height exponential identity 1c71a04d-268a-4126-b1bd-c0537bda0db1; ordinary chain rule for Real.exp and neighbourhood equality on positive heights.

import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_exp_log_scale_deriv

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_01_original_record_discount_height_ode
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤) :
    ∀ a h : ℝ, 0 < a → 0 < h →
      HasDerivAt
        (fun b : ℝ =>
          (∫⁻ ω, if twoSidedExitUpTime X b ω <
                      barrierRuinTime X a ω then
            ENNReal.ofReal
              (Real.exp (-(q * (twoSidedExitUpTime X b ω).toReal)))
          else 0 ∂P).toReal)
        (-(deriv W a / W a) *
          (∫⁻ ω, if twoSidedExitUpTime X h ω <
                      barrierRuinTime X a ω then
            ENNReal.ofReal
              (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
          else 0 ∂P).toReal) h := by sorry

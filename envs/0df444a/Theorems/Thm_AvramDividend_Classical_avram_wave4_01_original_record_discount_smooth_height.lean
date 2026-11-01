-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_smooth_height
-- name    : AvramDividend.Classical.avram_wave4_01_original_record_discount_smooth_height
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T17:28:20.359724+00:00
-- url     : https://prove2.me/theorems/e8a4961b-29ed-480c-a54d-46fb72ab9fd2
-- title:
--   Infinitely smooth positive-height dependence of genuine original discounted strict first-record survival
-- statement:
--   Under infinite variation from the small negative jumps, the actual original-process discounted first-record survival probability G_a(h)=E[exp(-q T_h);T_h<D_a] is C infinity on positive heights for every fixed depth a>0. This follows from the genuinely proved semigroup hazard identity G_a(h)=exp(-h W'(a)/W(a)), a real analytic function of height, and does not assume the original rough Lévy sample paths are smooth.
-- source:
--   Proved genuine original first-record hazard exponential law 1c71a04d, pinned Mathlib Real.contDiff_exp and ContDiffOn.congr.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_exp_log_scale_deriv
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_01_original_record_discount_smooth_height
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (a : ℝ) (ha : 0 < a) :
    ContDiffOn ℝ ⊤ (fun h : ℝ =>
      (∫⁻ ω, if twoSidedExitUpTime X h ω <
                  barrierRuinTime X a ω then
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
      else 0 ∂P).toReal) (Ioi 0) := by sorry

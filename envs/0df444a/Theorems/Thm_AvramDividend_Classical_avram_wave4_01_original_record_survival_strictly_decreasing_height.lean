-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_survival_strictly_decreasing_height
-- name    : AvramDividend.Classical.avram_wave4_01_original_record_survival_strictly_decreasing_height
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T19:21:45.378419+00:00
-- url     : https://prove2.me/theorems/d8f525b4-ca3d-462a-b27a-f49b44fe8a31
-- title:
--   Strict spatial decrease of actual killed original first-record discounted survival for pure infinite small-jump variation
-- statement:
--   Under q>0, the pure infinite-small-jump variation condition without Standing, and a positive solution φ to ψ(φ)=q, the genuine original killed upward-record discount G_a(h)=E[e^{-qT_h};T_h<D_a] is strictly decreasing in positive record height h for each a>0. The exact source semigroup exponential formula gives rate κ(a)=W′(a)/W(a), which is at least φ>0.
-- source:
--   Proved genuine avram_wave4_01_original_record_discount_exp_log_scale_deriv and avram_wave4_01_original_record_log_slope_ge_positive_esscher_root.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_exp_log_scale_deriv
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_log_slope_ge_positive_esscher_root
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_01_original_record_survival_strictly_decreasing_height
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (a : ℝ) (ha : 0 < a) :
    StrictAntiOn (fun h : ℝ =>
      (∫⁻ ω, if twoSidedExitUpTime X h ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitUpTime X h ω).toReal)))
      else 0 ∂P).toReal) (Ioi 0) := by sorry

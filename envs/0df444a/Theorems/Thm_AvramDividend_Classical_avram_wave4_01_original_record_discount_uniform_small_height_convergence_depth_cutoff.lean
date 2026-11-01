-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_uniform_small_height_convergence_depth_cutoff
-- name    : AvramDividend.Classical.avram_wave4_01_original_record_discount_uniform_small_height_convergence_depth_cutoff
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:52:35.808+00:00
-- url     : https://prove2.me/theorems/ebac08a9-d393-405b-9419-f9e60fd3645e
-- title:
--   Uniform original killed first-record small-height convergence across all depths above a positive cutoff
-- statement:
--   For the actual first strict upward record T_h and reflected drawdown ruin D_a under pure infinite-small-negative-jump variation, positive q, and a fixed positive lower drawdown cutoff delta, the killed discounted strict-record survival G_a(h) converges to 1 as positive h decreases to zero uniformly across every a>=delta. Precisely for each epsilon>0, for sufficiently small h>0, simultaneously for all a>=delta, 1-epsilon<=G_a(h)<=1. This is stronger than the separately Proved pointwise small-height limit and uses the newly Proved source-uniform linear lower estimate and the genuine root-based strict upper bound.
-- source:
--   Newly canonically Proved original source depth-uniform linear bound 10b785dc-9eb2-447d-b804-9d127cfabaf2 and Proved strict discounted survival upper bound 1a3528af-4aa0-4337-b8a4-12dabfe9325e.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_uniform_small_height_linear_lower_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_reflected_record_discount_strict_lt_one_of_root
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_01_original_record_discount_uniform_small_height_convergence_depth_cutoff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (δ : ℝ) (hδ : 0 < δ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      ∀ a : ℝ, δ ≤ a →
        1 - ε ≤
          (∫⁻ ω, if twoSidedExitUpTime X h ω <
              barrierRuinTime X a ω then
            ENNReal.ofReal (Real.exp (-(q *
              (twoSidedExitUpTime X h ω).toReal)))
          else 0 ∂P).toReal ∧
        (∫⁻ ω, if twoSidedExitUpTime X h ω <
              barrierRuinTime X a ω then
            ENNReal.ofReal (Real.exp (-(q *
              (twoSidedExitUpTime X h ω).toReal)))
          else 0 ∂P).toReal ≤ 1 := by sorry

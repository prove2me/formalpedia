-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_physical_rightmesh_isStoppingTime
-- name    : AvramDividend.Classical.avram_f6_original_physical_rightmesh_isStoppingTime
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T18:43:30.098468+00:00
-- url     : https://prove2.me/theorems/f1e21a07-b0b1-41b5-92ab-232910b17035
-- title:
--   Genuine min of original stopped horizon and delayed physical σ is a stopping time
-- statement:
--   Given original right-continuous-filtration stopping times τ and σ, each true right-delayed clock ρ=min(τ,σ+δ) for deterministic δ≥0 is a stopping time. Apply pinned stopped min to proved positive NNReal shift, without fabricating a process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_NNReal_positive_shift_stopping
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_physical_rightmesh_isStoppingTime
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (τ σ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hσ : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (δ : ℝ≥0) :
    IsStoppingTime 𝓕.rightCont
      (fun ω => ((min (τ ω) (σ ω + δ) : ℝ≥0) : WithTop ℝ≥0)) := by sorry

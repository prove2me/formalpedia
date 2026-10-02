-- Prove2me | Theorems.Thm_BookProof_HashimotoShiftInvert_shiftRange_orthogonal_eq_bot
-- name    : BookProof.HashimotoShiftInvert.shiftRange_orthogonal_eq_bot
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-02T09:43:05.620325+00:00
-- url     : https://prove2.me/theorems/7120b4f1-0e9f-4a86-a5e4-98ed4a6c7971
-- title:
--   The Lean 4 theorem `shiftRange_orthogonal_eq_bot` in the `ChapterHashimotoShiftInvert` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `shiftRange_orthogonal_eq_bot` in the `ChapterHashimotoShiftInvert` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHashimotoShiftInvert.lean

-- Generated from ChapterHashimotoShiftInvert.lean — theorem BookProof.HashimotoShiftInvert.shiftRange_orthogonal_eq_bot
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsFriedrichsLimit
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Mathlib
import Definitions.Def_ChapterHashimotoShiftInvert
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterComplexShiftCore
open BookProof.QgOuterFockFL
open BookProof.HashimotoShiftInvert

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {Dom : Submodule ℂ F}



open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology

theorem BookProof.HashimotoShiftInvert.shiftRange_orthogonal_eq_bot {A : Dom →ₗ[ℂ] F}
    (hpos : ∀ x : Dom, 0 ≤ quadForm A x)
    (hsa : ∀ w u : F, (∀ v : Dom, (inner ℂ (A v) w : ℂ) = inner ℂ (v : F) u) →
      ∃ h : w ∈ Dom, A ⟨w, h⟩ = u)
    {γ : ℝ} (hγ : 0 < γ) : (shiftRange A γ)ᗮ = ⊥ := by sorry

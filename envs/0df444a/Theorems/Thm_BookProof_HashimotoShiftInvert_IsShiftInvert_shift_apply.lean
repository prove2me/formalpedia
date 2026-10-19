-- Prove2me | Theorems.Thm_BookProof_HashimotoShiftInvert_IsShiftInvert_shift_apply
-- name    : BookProof.HashimotoShiftInvert.IsShiftInvert.shift_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T19:35:23.451755+00:00
-- url     : https://prove2.me/theorems/a17835c6-a196-406f-8ac8-ed6458d251c2
-- title:
--   The Lean 4 theorem `shift_apply` in the `ChapterHashimotoShiftInvert` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `shift_apply` in the `ChapterHashimotoShiftInvert` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHashimotoShiftInvert.lean

-- Generated from ChapterHashimotoShiftInvert.lean — theorem BookProof.HashimotoShiftInvert.IsShiftInvert.shift_apply
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsFriedrichsLimit
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Mathlib
import Definitions.Def_ChapterHashimotoShiftInvert
import Definitions.Def_ChapterAbelianDiagonalCountable
import Definitions.Def_ChapterComplexShiftCore
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.HashimotoShiftInvert



open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {Dom : Submodule ℂ F}

theorem BookProof.HashimotoShiftInvert.IsShiftInvert.shift_apply {A : Dom →ₗ[ℂ] F} {γ : ℝ} {R : F →L[ℂ] F}
    (h : IsShiftInvert A γ R) (u : F) :
    A ⟨R u, (h.2 u).choose⟩ + (γ : ℂ) • R u = u := by sorry

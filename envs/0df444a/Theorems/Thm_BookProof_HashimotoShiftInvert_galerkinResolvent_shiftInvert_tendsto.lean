-- Prove2me | Theorems.Thm_BookProof_HashimotoShiftInvert_galerkinResolvent_shiftInvert_tendsto
-- name    : BookProof.HashimotoShiftInvert.galerkinResolvent_shiftInvert_tendsto
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T05:01:07.250378+00:00
-- url     : https://prove2.me/theorems/be88bfad-7c5b-4ca6-ba25-3d31ef39c99b
-- title:
--   The Lean 4 theorem `galerkinResolvent_shiftInvert_tendsto` in the `ChapterHashimotoShiftInvert` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `galerkinResolvent_shiftInvert_tendsto` in the `ChapterHashimotoShiftInvert` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHashimotoShiftInvert.lean

-- Generated from ChapterHashimotoShiftInvert.lean — theorem BookProof.HashimotoShiftInvert.galerkinResolvent_shiftInvert_tendsto
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsFriedrichsLimit
import Mathlib
import Definitions.Def_ChapterHashimotoShiftInvert
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterComplexShiftCore
open BookProof.HermiteGalerkin
open BookProof.HashimotoShiftInvert



open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {Dom : Submodule ℂ F}

theorem BookProof.HashimotoShiftInvert.galerkinResolvent_shiftInvert_tendsto {A : Dom →ₗ[ℂ] F} {γ : ℝ} {R : F →L[ℂ] F}
    (h : IsShiftInvert A γ R) (hsym : SymmetricOn Dom A) (b : HilbertBasis ℕ ℂ F)
    {z : ℂ} (hz : z.im ≠ 0) (u : F) :
    Tendsto (fun m : ℕ => resolvent (galerkinCompression R b m) z u) atTop
      (nhds (resolvent R z u)) := by sorry

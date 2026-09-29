-- Prove2me | Theorems.Thm_BookProof_FarisLavine_conj_mul_ofReal
-- name    : BookProof.FarisLavine.conj_mul_ofReal
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:42:52.702985+00:00
-- url     : https://prove2.me/theorems/cb0fa34c-dcb0-4b55-9284-e6f47bda1db4
-- title:
--   The Lean 4 theorem `conj_mul_ofReal` in the `ChapterFarisLavine` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `conj_mul_ofReal` in the `ChapterFarisLavine` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFarisLavine.lean

-- Generated from ChapterFarisLavine.lean — theorem BookProof.FarisLavine.conj_mul_ofReal
import Mathlib
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesFarisLavineLift
open BookProof.FarisLavine




variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}




open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.LpNat




open scoped ENNReal

theorem BookProof.FarisLavine.conj_mul_ofReal (b : ℝ) (z : ℂ) :
    (b : ℂ) * z * (starRingEnd ℂ) z = ((b * Complex.normSq z : ℝ) : ℂ) := by sorry

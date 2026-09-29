-- Prove2me | Theorems.Thm_BookProof_FarisLavine_hasZeroDeficiencyOn_of_farisLavine
-- name    : BookProof.FarisLavine.hasZeroDeficiencyOn_of_farisLavine
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:23:30.48878+00:00
-- url     : https://prove2.me/theorems/f3e65dd3-f01a-4716-9d95-77c04898cc37
-- title:
--   The Lean 4 theorem `hasZeroDeficiencyOn_of_farisLavine` in the `ChapterFarisLavine` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `hasZeroDeficiencyOn_of_farisLavine` in the `ChapterFarisLavine` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFarisLavine.lean

-- Generated from ChapterFarisLavine.lean — theorem BookProof.FarisLavine.hasZeroDeficiencyOn_of_farisLavine
import Mathlib
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesFarisLavineLift
import Definitions.Def_ChapterFarisLavineCore
open BookProof.FarisLavine




variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}




open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.LpNat




open scoped ENNReal























open BookProof.NavierStokesFlow

theorem BookProof.FarisLavine.hasZeroDeficiencyOn_of_farisLavine [CompleteSpace F]
    (D : Submodule ℂ F) (H N : D →ₗ[ℂ] D) (c : ℝ)
    (hH : SymmetricOn D (D.subtype.comp H)) (hN : SymmetricOn D (D.subtype.comp N))
    (hc : 0 ≤ c)
    (hNpos : ∀ x : D, 0 ≤ quadForm (D.subtype.comp N) x)
    (hNsurj : ∀ f : F, ∃ x : D, (N x : F) + (x : F) = f)
    (hcomm : ∀ x : D, |commForm (D.subtype.comp H) (D.subtype.comp N) x|
      ≤ c * quadForm (D.subtype.comp N) x) :
    HasZeroDeficiencyOn D H := by sorry

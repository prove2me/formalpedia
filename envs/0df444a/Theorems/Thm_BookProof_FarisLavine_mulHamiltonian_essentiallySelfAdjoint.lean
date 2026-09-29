-- Prove2me | Theorems.Thm_BookProof_FarisLavine_mulHamiltonian_essentiallySelfAdjoint
-- name    : BookProof.FarisLavine.mulHamiltonian_essentiallySelfAdjoint
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:23:13.990596+00:00
-- url     : https://prove2.me/theorems/a27ad299-70a9-4bf1-bb0c-05238fa6dba4
-- title:
--   The Lean 4 theorem `mulHamiltonian_essentiallySelfAdjoint` in the `ChapterFarisLavine` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `mulHamiltonian_essentiallySelfAdjoint` in the `ChapterFarisLavine` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFarisLavine.lean

-- Generated from ChapterFarisLavine.lean — theorem BookProof.FarisLavine.mulHamiltonian_essentiallySelfAdjoint
import Mathlib
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesFarisLavineLift
import Definitions.Def_ChapterFarisLavineCore
open BookProof.FarisLavine




variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}




open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.LpNat




open scoped ENNReal

theorem BookProof.FarisLavine.mulHamiltonian_essentiallySelfAdjoint (lam : ℕ → ℝ) :
    EssentiallySelfAdjointOn (mulSymbolDomain lam) (mulHamiltonian lam) := by sorry

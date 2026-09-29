-- Prove2me | Theorems.Thm_BookProof_FarisLavine_essentiallySelfAdjointOn_iff_hasZeroDeficiencyOn
-- name    : BookProof.FarisLavine.essentiallySelfAdjointOn_iff_hasZeroDeficiencyOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:21:46.615302+00:00
-- url     : https://prove2.me/theorems/465d4655-9725-4a90-ac94-20f9b52cd32c
-- title:
--   The Lean 4 theorem `essentiallySelfAdjointOn_iff_hasZeroDeficiencyOn` in the `ChapterFarisLavine` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `essentiallySelfAdjointOn_iff_hasZeroDeficiencyOn` in the `ChapterFarisLavine` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFarisLavine.lean

-- Generated from ChapterFarisLavine.lean — theorem BookProof.FarisLavine.essentiallySelfAdjointOn_iff_hasZeroDeficiencyOn
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

theorem BookProof.FarisLavine.essentiallySelfAdjointOn_iff_hasZeroDeficiencyOn
    (D : Submodule ℂ F) (H : D →ₗ[ℂ] D) :
    EssentiallySelfAdjointOn D (D.subtype.comp H) ↔ HasZeroDeficiencyOn D H := by sorry

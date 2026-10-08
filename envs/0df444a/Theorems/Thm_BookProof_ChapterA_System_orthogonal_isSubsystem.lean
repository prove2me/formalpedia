-- Prove2me | Theorems.Thm_BookProof_ChapterA_System_orthogonal_isSubsystem
-- name    : BookProof.ChapterA.System.orthogonal_isSubsystem
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-06T04:24:50.492602+00:00
-- url     : https://prove2.me/theorems/c428b042-fab5-4bbc-99ba-a2f70e68405d
-- title:
--   `BookProof.ChapterA.System.orthogonal_isSubsystem` (M : System 𝔽 V) (hM : IsNormal M) {W : Submodule 𝔽 V} (hW : IsSubsystem M W) : IsSubsystem M Wᗮ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA`.
--
--   `BookProof.ChapterA.System.orthogonal_isSubsystem` (M : System 𝔽 V) (hM : IsNormal M) {W : Submodule 𝔽 V} (hW : IsSubsystem M W) : IsSubsystem M Wᗮ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA.System.orthogonal_isSubsystem`.

-- Generated from ChapterA.lean — theorem BookProof.ChapterA.System.orthogonal_isSubsystem
import Mathlib
import Definitions.Def_ChapterA
open BookProof.ChapterA
open BookProof.ChapterA

variable {𝔽 : Type*} [RCLike 𝔽] {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace 𝔽 V] [CompleteSpace V]


open scoped ComplexConjugate InnerProductSpace

theorem BookProof.ChapterA.System.orthogonal_isSubsystem (M : System 𝔽 V) (hM : IsNormal M)
    {W : Submodule 𝔽 V} (hW : IsSubsystem M W) : IsSubsystem M Wᗮ := by sorry

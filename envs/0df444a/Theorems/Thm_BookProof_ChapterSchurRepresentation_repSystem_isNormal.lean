-- Prove2me | Theorems.Thm_BookProof_ChapterSchurRepresentation_repSystem_isNormal
-- name    : BookProof.ChapterSchurRepresentation.repSystem_isNormal
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T01:03:08.343977+00:00
-- url     : https://prove2.me/theorems/2ba2da56-c944-4064-ab84-36dfb0042294
-- title:
--   `BookProof.ChapterSchurRepresentation.repSystem_isNormal` {G : Type*} [Group G] (U : G →* (V ≃ₗᵢ[ℂ] V)) : (repSystem U).IsNormal
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSchurRepresentation`.
--
--   `BookProof.ChapterSchurRepresentation.repSystem_isNormal` {G : Type*} [Group G] (U : G →* (V ≃ₗᵢ[ℂ] V)) : (repSystem U).IsNormal
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSchurRepresentation.repSystem_isNormal`.

-- Generated from ChapterSchurRepresentation.lean — theorem BookProof.ChapterSchurRepresentation.repSystem_isNormal
import Definitions.Def_ChapterSchurIrreducible
import Mathlib
import Definitions.Def_ChapterSchurRepresentation
import Definitions.Def_ChapterA
open BookProof.ChapterA
open BookProof.ChapterA.System
open BookProof.ChapterSchurRepresentation


open scoped ComplexConjugate InnerProductSpace


open BookProof.ChapterA BookProof.ChapterA.System BookProof.ChapterSchurIrreducible

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem BookProof.ChapterSchurRepresentation.repSystem_isNormal {G : Type*} [Group G] (U : G →* (V ≃ₗᵢ[ℂ] V)) :
    (repSystem U).IsNormal := by sorry

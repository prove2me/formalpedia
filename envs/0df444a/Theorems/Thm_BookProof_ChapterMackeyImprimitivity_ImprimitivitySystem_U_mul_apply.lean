-- Prove2me | Theorems.Thm_BookProof_ChapterMackeyImprimitivity_ImprimitivitySystem_U_mul_apply
-- name    : BookProof.ChapterMackeyImprimitivity.ImprimitivitySystem.U_mul_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:49:18.9849+00:00
-- url     : https://prove2.me/theorems/53167fbc-b02b-48d7-9788-5ccc654015db
-- title:
--   `BookProof.ChapterMackeyImprimitivity.ImprimitivitySystem.U_mul_apply` (g h : G) (ψ : E) : S.U g (S.U h ψ) = S.U (g * h) ψ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMackeyImprimitivity`.
--
--   `BookProof.ChapterMackeyImprimitivity.ImprimitivitySystem.U_mul_apply` (g h : G) (ψ : E) : S.U g (S.U h ψ) = S.U (g * h) ψ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMackeyImprimitivity.ImprimitivitySystem.U_mul_apply`.

-- Generated from ChapterMackeyImprimitivity.lean — theorem BookProof.ChapterMackeyImprimitivity.ImprimitivitySystem.U_mul_apply
import Mathlib
import Definitions.Def_ChapterMackeyImprimitivity
open BookProof.ChapterMackeyImprimitivity
open BookProof.ChapterMackeyImprimitivity


open scoped InnerProductSpace
open Finset


variable {G : Type*} [Group G] {X : Type*} [Fintype X] [MulAction G X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable (S : ImprimitivitySystem G X E)

theorem BookProof.ChapterMackeyImprimitivity.ImprimitivitySystem.U_mul_apply (g h : G) (ψ : E) : S.U g (S.U h ψ) = S.U (g * h) ψ := by sorry

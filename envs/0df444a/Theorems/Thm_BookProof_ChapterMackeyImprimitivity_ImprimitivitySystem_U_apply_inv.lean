-- Prove2me | Theorems.Thm_BookProof_ChapterMackeyImprimitivity_ImprimitivitySystem_U_apply_inv
-- name    : BookProof.ChapterMackeyImprimitivity.ImprimitivitySystem.U_apply_inv
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:49:23.365402+00:00
-- url     : https://prove2.me/theorems/fe3baebb-afa7-408a-b84a-b4131bd52cd8
-- title:
--   `BookProof.ChapterMackeyImprimitivity.ImprimitivitySystem.U_apply_inv` (g : G) (ψ : E) : S.U g (S.U g⁻¹ ψ) = ψ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMackeyImprimitivity`.
--
--   `BookProof.ChapterMackeyImprimitivity.ImprimitivitySystem.U_apply_inv` (g : G) (ψ : E) : S.U g (S.U g⁻¹ ψ) = ψ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMackeyImprimitivity.ImprimitivitySystem.U_apply_inv`.

-- Generated from ChapterMackeyImprimitivity.lean — theorem BookProof.ChapterMackeyImprimitivity.ImprimitivitySystem.U_apply_inv
import Mathlib
import Definitions.Def_ChapterMackeyImprimitivity
open BookProof.ChapterMackeyImprimitivity
open BookProof.ChapterMackeyImprimitivity


open scoped InnerProductSpace
open Finset


variable {G : Type*} [Group G] {X : Type*} [Fintype X] [MulAction G X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable (S : ImprimitivitySystem G X E)

theorem BookProof.ChapterMackeyImprimitivity.ImprimitivitySystem.U_apply_inv (g : G) (ψ : E) : S.U g (S.U g⁻¹ ψ) = ψ := by sorry

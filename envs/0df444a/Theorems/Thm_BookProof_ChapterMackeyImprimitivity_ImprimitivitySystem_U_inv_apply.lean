-- Prove2me | Theorems.Thm_BookProof_ChapterMackeyImprimitivity_ImprimitivitySystem_U_inv_apply
-- name    : BookProof.ChapterMackeyImprimitivity.ImprimitivitySystem.U_inv_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:49:26.790055+00:00
-- url     : https://prove2.me/theorems/ccd6f899-e110-4663-a665-4563377072c7
-- title:
--   `BookProof.ChapterMackeyImprimitivity.ImprimitivitySystem.U_inv_apply` (g : G) (ψ : E) : S.U g⁻¹ (S.U g ψ) = ψ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMackeyImprimitivity`.
--
--   `BookProof.ChapterMackeyImprimitivity.ImprimitivitySystem.U_inv_apply` (g : G) (ψ : E) : S.U g⁻¹ (S.U g ψ) = ψ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMackeyImprimitivity.ImprimitivitySystem.U_inv_apply`.

-- Generated from ChapterMackeyImprimitivity.lean — theorem BookProof.ChapterMackeyImprimitivity.ImprimitivitySystem.U_inv_apply
import Mathlib
import Definitions.Def_ChapterMackeyImprimitivity
open BookProof.ChapterMackeyImprimitivity
open BookProof.ChapterMackeyImprimitivity


open scoped InnerProductSpace
open Finset


variable {G : Type*} [Group G] {X : Type*} [Fintype X] [MulAction G X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable (S : ImprimitivitySystem G X E)

theorem BookProof.ChapterMackeyImprimitivity.ImprimitivitySystem.U_inv_apply (g : G) (ψ : E) : S.U g⁻¹ (S.U g ψ) = ψ := by sorry

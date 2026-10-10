-- Prove2me | Theorems.Thm_BookProof_ChapterMackeyImprimitivity_stabilizer_comm_fibre
-- name    : BookProof.ChapterMackeyImprimitivity.stabilizer_comm_fibre
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:51:08.045631+00:00
-- url     : https://prove2.me/theorems/8cc9978b-4293-4c91-a929-6269793b9fa3
-- title:
--   `BookProof.ChapterMackeyImprimitivity.stabilizer_comm_fibre` {h : G} (hh : h ∈ MulAction.stabilizer G x₀) (v : E) : S.U h (S.p x₀ v) = S.p x₀ (S.U h v)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMackeyImprimitivity`.
--
--   `BookProof.ChapterMackeyImprimitivity.stabilizer_comm_fibre` {h : G} (hh : h ∈ MulAction.stabilizer G x₀) (v : E) : S.U h (S.p x₀ v) = S.p x₀ (S.U h v)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMackeyImprimitivity.stabilizer_comm_fibre`.

-- Generated from ChapterMackeyImprimitivity.lean — theorem BookProof.ChapterMackeyImprimitivity.stabilizer_comm_fibre
import Mathlib
import Definitions.Def_ChapterMackeyImprimitivity
open BookProof.ChapterMackeyImprimitivity


open scoped InnerProductSpace
open Finset


variable {G : Type*} [Group G] {X : Type*} [Fintype X] [MulAction G X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable (S : ImprimitivitySystem G X E)
variable (S : ImprimitivitySystem G X E) (x₀ : X) (s : X → G)
variable {S x₀ s}

theorem BookProof.ChapterMackeyImprimitivity.stabilizer_comm_fibre {h : G} (hh : h ∈ MulAction.stabilizer G x₀) (v : E) :
    S.U h (S.p x₀ v) = S.p x₀ (S.U h v) := by sorry

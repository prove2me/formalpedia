-- Prove2me | Theorems.Thm_BookProof_ChapterMackeyImprimitivity_cocycle_mem_stabilizer
-- name    : BookProof.ChapterMackeyImprimitivity.cocycle_mem_stabilizer
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T13:51:37.232899+00:00
-- url     : https://prove2.me/theorems/b949485d-c767-4712-87cb-5ccab6c85832
-- title:
--   `BookProof.ChapterMackeyImprimitivity.cocycle_mem_stabilizer` (hs : ∀ x, s x • x₀ = x) (g : G) (x : X) : cocycle s g x ∈ MulAction.stabilizer G x₀
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMackeyImprimitivity`.
--
--   `BookProof.ChapterMackeyImprimitivity.cocycle_mem_stabilizer` (hs : ∀ x, s x • x₀ = x) (g : G) (x : X) : cocycle s g x ∈ MulAction.stabilizer G x₀
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMackeyImprimitivity.cocycle_mem_stabilizer`.

-- Generated from ChapterMackeyImprimitivity.lean — theorem BookProof.ChapterMackeyImprimitivity.cocycle_mem_stabilizer
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

theorem BookProof.ChapterMackeyImprimitivity.cocycle_mem_stabilizer (hs : ∀ x, s x • x₀ = x) (g : G) (x : X) :
    cocycle s g x ∈ MulAction.stabilizer G x₀ := by sorry

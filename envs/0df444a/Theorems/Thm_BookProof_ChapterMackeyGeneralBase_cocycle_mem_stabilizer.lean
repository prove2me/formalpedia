-- Prove2me | Theorems.Thm_BookProof_ChapterMackeyGeneralBase_cocycle_mem_stabilizer
-- name    : BookProof.ChapterMackeyGeneralBase.cocycle_mem_stabilizer
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-04T13:49:40.434982+00:00
-- url     : https://prove2.me/theorems/25a68047-bfad-448c-a152-93b1d00accf0
-- title:
--   The Lean 4 theorem `cocycle_mem_stabilizer` in the `ChapterMackeyGeneralBase` chapter of the timepiece formalization
-- statement:
--   Formal statement of `BookProof.ChapterMackeyGeneralBase.cocycle_mem_stabilizer` from the timepiece Lean 4 formalization.
-- source:
--   https://github.com/leonardopedro/timepiece

-- Generated from ChapterMackeyGeneralBase.lean — theorem BookProof.ChapterMackeyGeneralBase.cocycle_mem_stabilizer
import Mathlib
import Definitions.Def_ChapterMackeyGeneralBase
import Definitions.Def_ChapterMackeyImprimitivity
import Definitions.Def_ChapterA4
open BookProof.ChapterMackeyImprimitivity
open BookProof.ChapterMackeyImprimitivity
open BookProof.ChapterMackeyGeneralBase

variable {G : Type*} [Group G] {X : Type*} [MulAction G X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable (S : ImprimitivitySystem G X E)
variable (S : ImprimitivitySystem G X E) (x₀ : X) (s : X → G)
variable {S x₀ s}


open scoped InnerProductSpace

theorem BookProof.ChapterMackeyGeneralBase.cocycle_mem_stabilizer (hs : ∀ x, s x • x₀ = x) (g : G) (x : X) :
    cocycle s g x ∈ MulAction.stabilizer G x₀ := by sorry

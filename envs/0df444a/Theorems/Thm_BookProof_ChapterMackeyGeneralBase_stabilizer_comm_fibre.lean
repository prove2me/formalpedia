-- Prove2me | Theorems.Thm_BookProof_ChapterMackeyGeneralBase_stabilizer_comm_fibre
-- name    : BookProof.ChapterMackeyGeneralBase.stabilizer_comm_fibre
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-04T20:21:33.248344+00:00
-- url     : https://prove2.me/theorems/793e19c5-fa2b-431c-bcc8-348f50a05eef
-- title:
--   The Lean 4 theorem `stabilizer_comm_fibre` in the `ChapterMackeyGeneralBase` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `stabilizer_comm_fibre` in the `ChapterMackeyGeneralBase` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterMackeyGeneralBase.lean

-- Generated from ChapterMackeyGeneralBase.lean — theorem BookProof.ChapterMackeyGeneralBase.stabilizer_comm_fibre
import Definitions.Def_ChapterOrthogonalSums
import Mathlib
import Definitions.Def_ChapterMackeyGeneralBase
import Definitions.Def_ChapterMackeyImprimitivity
import Definitions.Def_ChapterMackeyImprimitivity
open BookProof.ChapterMackeyImprimitivity
open BookProof.ChapterMackeyImprimitivity


open scoped InnerProductSpace


open BookProof.ChapterOrthogonalSums

variable {G : Type*} [Group G] {X : Type*} [MulAction G X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable (S : BookProof.ChapterMackeyGeneralBase.ImprimitivitySystem G X E)
variable (S : BookProof.ChapterMackeyGeneralBase.ImprimitivitySystem G X E) (x₀ : X) (s : X → G)
variable {S x₀ s}

theorem BookProof.ChapterMackeyGeneralBase.stabilizer_comm_fibre {h : G} (hh : h ∈ MulAction.stabilizer G x₀) (v : E) :
    S.U h (S.p x₀ v) = S.p x₀ (S.U h v) := by sorry

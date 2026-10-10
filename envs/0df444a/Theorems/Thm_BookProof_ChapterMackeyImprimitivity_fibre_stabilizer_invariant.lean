-- Prove2me | Theorems.Thm_BookProof_ChapterMackeyImprimitivity_fibre_stabilizer_invariant
-- name    : BookProof.ChapterMackeyImprimitivity.fibre_stabilizer_invariant
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:50:53.107367+00:00
-- url     : https://prove2.me/theorems/7f6bf5a6-84a3-48f3-a15d-d050f2bf0ea4
-- title:
--   `BookProof.ChapterMackeyImprimitivity.fibre_stabilizer_invariant` {h : G} (hh : h ∈ MulAction.stabilizer G x₀) {v : E} (hv : S.p x₀ v = v) : S.p x₀ (S.U h v) = S.U h v
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMackeyImprimitivity`.
--
--   `BookProof.ChapterMackeyImprimitivity.fibre_stabilizer_invariant` {h : G} (hh : h ∈ MulAction.stabilizer G x₀) {v : E} (hv : S.p x₀ v = v) : S.p x₀ (S.U h v) = S.U h v
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMackeyImprimitivity.fibre_stabilizer_invariant`.

-- Generated from ChapterMackeyImprimitivity.lean — theorem BookProof.ChapterMackeyImprimitivity.fibre_stabilizer_invariant
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

theorem BookProof.ChapterMackeyImprimitivity.fibre_stabilizer_invariant {h : G} (hh : h ∈ MulAction.stabilizer G x₀) {v : E}
    (hv : S.p x₀ v = v) : S.p x₀ (S.U h v) = S.U h v := by sorry

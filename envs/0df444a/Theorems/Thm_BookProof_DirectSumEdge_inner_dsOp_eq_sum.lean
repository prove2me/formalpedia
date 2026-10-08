-- Prove2me | Theorems.Thm_BookProof_DirectSumEdge_inner_dsOp_eq_sum
-- name    : BookProof.DirectSumEdge.inner_dsOp_eq_sum
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:58:01.912984+00:00
-- url     : https://prove2.me/theorems/ccdbf3e5-8bd0-4ef2-a87c-f2501fd3b936
-- title:
--   `BookProof.DirectSumEdge.inner_dsOp_eq_sum` (H : ∀ i, D i →ₗ[ℂ] G i) (x : dsCore D) : (inner ℂ (x : lp G 2) (dsOp H x : lp G 2) : ℂ) = ∑ i ∈ supportFinset x, (inner ℂ (((x : lp G 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDirectSumEdge`.
--
--   `BookProof.DirectSumEdge.inner_dsOp_eq_sum` (H : ∀ i, D i →ₗ[ℂ] G i) (x : dsCore D) : (inner ℂ (x : lp G 2) (dsOp H x : lp G 2) : ℂ) = ∑ i ∈ supportFinset x, (inner ℂ (((x : lp G 2) : ∀ i, G i) i) (H i ⟨((x : lp G 2) : ∀ i, G i) i, x.2.2 i⟩) : ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.DirectSumEdge.inner_dsOp_eq_sum`.

-- Generated from ChapterDirectSumEdge.lean — theorem BookProof.DirectSumEdge.inner_dsOp_eq_sum
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterDirectSumEdge
import Definitions.Def_ChapterDirectSumEsa
open BookProof.DirectSumEsa
open BookProof.DirectSumEdge



open BookProof.FarisLavine BookProof.DirectSumEsa

noncomputable section

variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] {D : ∀ i, Submodule ℂ (G i)}

theorem BookProof.DirectSumEdge.inner_dsOp_eq_sum (H : ∀ i, D i →ₗ[ℂ] G i) (x : dsCore D) :
    (inner ℂ (x : lp G 2) (dsOp H x : lp G 2) : ℂ)
      = ∑ i ∈ supportFinset x,
          (inner ℂ (((x : lp G 2) : ∀ i, G i) i)
            (H i ⟨((x : lp G 2) : ∀ i, G i) i, x.2.2 i⟩) : ℂ) := by sorry

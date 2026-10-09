-- Prove2me | Theorems.Thm_BookProof_DirectSumEdge_inner_dsCore_eq_sum
-- name    : BookProof.DirectSumEdge.inner_dsCore_eq_sum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:57:29.112651+00:00
-- url     : https://prove2.me/theorems/06eb3219-36f8-4f9d-92cc-0e90127dc2e3
-- title:
--   `BookProof.DirectSumEdge.inner_dsCore_eq_sum` (x : dsCore D) (g : lp G 2) : (inner ℂ (x : lp G 2) g : ℂ) = ∑ i ∈ supportFinset x, (inner ℂ (((x : lp G 2) : ∀ i, G i) i) ((g : ∀ i,
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDirectSumEdge`.
--
--   `BookProof.DirectSumEdge.inner_dsCore_eq_sum` (x : dsCore D) (g : lp G 2) : (inner ℂ (x : lp G 2) g : ℂ) = ∑ i ∈ supportFinset x, (inner ℂ (((x : lp G 2) : ∀ i, G i) i) ((g : ∀ i, G i) i) : ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.DirectSumEdge.inner_dsCore_eq_sum`.

-- Generated from ChapterDirectSumEdge.lean — theorem BookProof.DirectSumEdge.inner_dsCore_eq_sum
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

theorem BookProof.DirectSumEdge.inner_dsCore_eq_sum (x : dsCore D) (g : lp G 2) :
    (inner ℂ (x : lp G 2) g : ℂ)
      = ∑ i ∈ supportFinset x,
          (inner ℂ (((x : lp G 2) : ∀ i, G i) i) ((g : ∀ i, G i) i) : ℂ) := by sorry

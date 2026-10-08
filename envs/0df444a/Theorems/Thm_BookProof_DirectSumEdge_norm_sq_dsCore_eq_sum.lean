-- Prove2me | Theorems.Thm_BookProof_DirectSumEdge_norm_sq_dsCore_eq_sum
-- name    : BookProof.DirectSumEdge.norm_sq_dsCore_eq_sum
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:57:31.929823+00:00
-- url     : https://prove2.me/theorems/e529ad5f-d8c4-466f-8d23-c97e2d6a7a00
-- title:
--   `BookProof.DirectSumEdge.norm_sq_dsCore_eq_sum` (x : dsCore D) : ‖(x : lp G 2)‖ ^ 2 = ∑ i ∈ supportFinset x, ‖((x : lp G 2) : ∀ i, G i) i‖ ^ 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDirectSumEdge`.
--
--   `BookProof.DirectSumEdge.norm_sq_dsCore_eq_sum` (x : dsCore D) : ‖(x : lp G 2)‖ ^ 2 = ∑ i ∈ supportFinset x, ‖((x : lp G 2) : ∀ i, G i) i‖ ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.DirectSumEdge.norm_sq_dsCore_eq_sum`.

-- Generated from ChapterDirectSumEdge.lean — theorem BookProof.DirectSumEdge.norm_sq_dsCore_eq_sum
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

theorem BookProof.DirectSumEdge.norm_sq_dsCore_eq_sum (x : dsCore D) :
    ‖(x : lp G 2)‖ ^ 2 = ∑ i ∈ supportFinset x, ‖((x : lp G 2) : ∀ i, G i) i‖ ^ 2 := by sorry

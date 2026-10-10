-- Prove2me | Theorems.Thm_BookProof_DirectSumEdge_quadForm_dsOp_eq_sum
-- name    : BookProof.DirectSumEdge.quadForm_dsOp_eq_sum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:58:03.784856+00:00
-- url     : https://prove2.me/theorems/12b9c179-ccf0-431c-9947-6986e9e45cc1
-- title:
--   `BookProof.DirectSumEdge.quadForm_dsOp_eq_sum` (H : ∀ i, D i →ₗ[ℂ] G i) (x : dsCore D) : quadForm (dsOp H) x = ∑ i ∈ supportFinset x, quadForm (H i) ⟨((x : lp G 2) : ∀ i, G i) i, x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDirectSumEdge`.
--
--   `BookProof.DirectSumEdge.quadForm_dsOp_eq_sum` (H : ∀ i, D i →ₗ[ℂ] G i) (x : dsCore D) : quadForm (dsOp H) x = ∑ i ∈ supportFinset x, quadForm (H i) ⟨((x : lp G 2) : ∀ i, G i) i, x.2.2 i⟩
--
--   Formalization note: Lean 4 identifier `BookProof.DirectSumEdge.quadForm_dsOp_eq_sum`.

-- Generated from ChapterDirectSumEdge.lean — theorem BookProof.DirectSumEdge.quadForm_dsOp_eq_sum
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterDirectSumEdge
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterFarisLavineCore
open BookProof.DirectSumEsa
open BookProof.DirectSumEdge



open BookProof.FarisLavine BookProof.DirectSumEsa

noncomputable section

variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] {D : ∀ i, Submodule ℂ (G i)}

theorem BookProof.DirectSumEdge.quadForm_dsOp_eq_sum (H : ∀ i, D i →ₗ[ℂ] G i) (x : dsCore D) :
    quadForm (dsOp H) x
      = ∑ i ∈ supportFinset x,
          quadForm (H i) ⟨((x : lp G 2) : ∀ i, G i) i, x.2.2 i⟩ := by sorry

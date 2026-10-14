-- Prove2me | Theorems.Thm_BookProof_DirectSumEsa_dsOp_single
-- name    : BookProof.DirectSumEsa.dsOp_single
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T14:13:16.055782+00:00
-- url     : https://prove2.me/theorems/cdfe9c73-e491-436a-a3ec-fda0ad68314d
-- title:
--   `BookProof.DirectSumEsa.dsOp_single` [DecidableEq ι] (H : ∀ i, D i →ₗ[ℂ] G i) (i : ι) (u : D i) : (dsOp H ⟨lp.single 2 i ((u : G i)), single_mem_dsCore i u⟩ : lp G 2) = lp.single 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDirectSumEsa`.
--
--   `BookProof.DirectSumEsa.dsOp_single` [DecidableEq ι] (H : ∀ i, D i →ₗ[ℂ] G i) (i : ι) (u : D i) : (dsOp H ⟨lp.single 2 i ((u : G i)), single_mem_dsCore i u⟩ : lp G 2) = lp.single 2 i (H i u)
--
--   Formalization note: Lean 4 identifier `BookProof.DirectSumEsa.dsOp_single`.

-- Generated from ChapterDirectSumEsa.lean — theorem BookProof.DirectSumEsa.dsOp_single
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterDirectSumEsa
import Theorems.Thm_BookProof_DirectSumEsa_single_mem_dsCore
open BookProof.DirectSumEsa


open scoped ENNReal


open BookProof.FarisLavine

noncomputable section

variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)]

variable {D : ∀ i, Submodule ℂ (G i)}

theorem BookProof.DirectSumEsa.dsOp_single [DecidableEq ι] (H : ∀ i, D i →ₗ[ℂ] G i) (i : ι) (u : D i) :
    (dsOp H ⟨lp.single 2 i ((u : G i)), single_mem_dsCore i u⟩ : lp G 2)
      = lp.single 2 i (H i u) := by sorry

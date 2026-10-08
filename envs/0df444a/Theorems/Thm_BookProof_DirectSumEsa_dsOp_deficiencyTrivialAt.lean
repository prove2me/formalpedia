-- Prove2me | Theorems.Thm_BookProof_DirectSumEsa_dsOp_deficiencyTrivialAt
-- name    : BookProof.DirectSumEsa.dsOp_deficiencyTrivialAt
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:58:59.253154+00:00
-- url     : https://prove2.me/theorems/60c6f1f5-00b3-4861-80cb-6c7fea0c88ad
-- title:
--   `BookProof.DirectSumEsa.dsOp_deficiencyTrivialAt` (H : ∀ i, D i →ₗ[ℂ] G i) {z : ℂ} (h : ∀ i, DeficiencyTrivialAt (D i) (H i) z) : DeficiencyTrivialAt (dsCore D) (dsOp H) z
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDirectSumEsa`.
--
--   `BookProof.DirectSumEsa.dsOp_deficiencyTrivialAt` (H : ∀ i, D i →ₗ[ℂ] G i) {z : ℂ} (h : ∀ i, DeficiencyTrivialAt (D i) (H i) z) : DeficiencyTrivialAt (dsCore D) (dsOp H) z
--
--   Formalization note: Lean 4 identifier `BookProof.DirectSumEsa.dsOp_deficiencyTrivialAt`.

-- Generated from ChapterDirectSumEsa.lean — theorem BookProof.DirectSumEsa.dsOp_deficiencyTrivialAt
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterFarisLavineCore
open BookProof.DirectSumEsa


open scoped ENNReal


open BookProof.FarisLavine

noncomputable section

variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)]

variable {D : ∀ i, Submodule ℂ (G i)}

theorem BookProof.DirectSumEsa.dsOp_deficiencyTrivialAt (H : ∀ i, D i →ₗ[ℂ] G i) {z : ℂ}
    (h : ∀ i, DeficiencyTrivialAt (D i) (H i) z) :
    DeficiencyTrivialAt (dsCore D) (dsOp H) z := by sorry

-- Prove2me | Theorems.Thm_BookProof_DirectSumEsa_dsOp_symmetricOn
-- name    : BookProof.DirectSumEsa.dsOp_symmetricOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:59:32.046976+00:00
-- url     : https://prove2.me/theorems/87ea27b9-9d61-43d0-a1ed-feb3b32d9d82
-- title:
--   `BookProof.DirectSumEsa.dsOp_symmetricOn` (H : ∀ i, D i →ₗ[ℂ] G i) (hsym : ∀ i, SymmetricOn (D i) (H i)) : SymmetricOn (dsCore D) (dsOp H)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDirectSumEsa`.
--
--   `BookProof.DirectSumEsa.dsOp_symmetricOn` (H : ∀ i, D i →ₗ[ℂ] G i) (hsym : ∀ i, SymmetricOn (D i) (H i)) : SymmetricOn (dsCore D) (dsOp H)
--
--   Formalization note: Lean 4 identifier `BookProof.DirectSumEsa.dsOp_symmetricOn`.

-- Generated from ChapterDirectSumEsa.lean — theorem BookProof.DirectSumEsa.dsOp_symmetricOn
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

theorem BookProof.DirectSumEsa.dsOp_symmetricOn (H : ∀ i, D i →ₗ[ℂ] G i) (hsym : ∀ i, SymmetricOn (D i) (H i)) :
    SymmetricOn (dsCore D) (dsOp H) := by sorry

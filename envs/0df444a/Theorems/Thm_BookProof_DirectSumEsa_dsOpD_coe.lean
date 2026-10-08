-- Prove2me | Theorems.Thm_BookProof_DirectSumEsa_dsOpD_coe
-- name    : BookProof.DirectSumEsa.dsOpD_coe
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:59:39.602783+00:00
-- url     : https://prove2.me/theorems/0055b13b-7e22-4335-9cb1-d819e4691ddc
-- title:
--   `BookProof.DirectSumEsa.dsOpD_coe` (A : ∀ i, D i →ₗ[ℂ] D i) (x : dsCore D) : ((dsOpD A x : dsCore D) : lp G 2) = (dsOp (fun i => (D i).subtype.comp (A i)) x : lp G 2)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDirectSumEsa`.
--
--   `BookProof.DirectSumEsa.dsOpD_coe` (A : ∀ i, D i →ₗ[ℂ] D i) (x : dsCore D) : ((dsOpD A x : dsCore D) : lp G 2) = (dsOp (fun i => (D i).subtype.comp (A i)) x : lp G 2)
--
--   Formalization note: Lean 4 identifier `BookProof.DirectSumEsa.dsOpD_coe`.

-- Generated from ChapterDirectSumEsa.lean — theorem BookProof.DirectSumEsa.dsOpD_coe
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterDirectSumEsa
open BookProof.DirectSumEsa


open scoped ENNReal


open BookProof.FarisLavine

noncomputable section

variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)]

variable {D : ∀ i, Submodule ℂ (G i)}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.DirectSumEsa.dsOpD_coe (A : ∀ i, D i →ₗ[ℂ] D i) (x : dsCore D) :
    ((dsOpD A x : dsCore D) : lp G 2)
      = (dsOp (fun i => (D i).subtype.comp (A i)) x : lp G 2) := by sorry

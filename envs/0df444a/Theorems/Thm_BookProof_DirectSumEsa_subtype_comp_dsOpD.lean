-- Prove2me | Theorems.Thm_BookProof_DirectSumEsa_subtype_comp_dsOpD
-- name    : BookProof.DirectSumEsa.subtype_comp_dsOpD
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:59:39.408503+00:00
-- url     : https://prove2.me/theorems/59fedcfb-6887-4266-8c55-4eff3880e889
-- title:
--   `BookProof.DirectSumEsa.subtype_comp_dsOpD` (A : ∀ i, D i →ₗ[ℂ] D i) : (dsCore D).subtype.comp (dsOpD A) = dsOp (fun i => (D i).subtype.comp (A i))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDirectSumEsa`.
--
--   `BookProof.DirectSumEsa.subtype_comp_dsOpD` (A : ∀ i, D i →ₗ[ℂ] D i) : (dsCore D).subtype.comp (dsOpD A) = dsOp (fun i => (D i).subtype.comp (A i))
--
--   Formalization note: Lean 4 identifier `BookProof.DirectSumEsa.subtype_comp_dsOpD`.

-- Generated from ChapterDirectSumEsa.lean — theorem BookProof.DirectSumEsa.subtype_comp_dsOpD
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

theorem BookProof.DirectSumEsa.subtype_comp_dsOpD (A : ∀ i, D i →ₗ[ℂ] D i) :
    (dsCore D).subtype.comp (dsOpD A) = dsOp (fun i => (D i).subtype.comp (A i)) := by sorry

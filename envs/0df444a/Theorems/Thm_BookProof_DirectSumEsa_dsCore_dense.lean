-- Prove2me | Theorems.Thm_BookProof_DirectSumEsa_dsCore_dense
-- name    : BookProof.DirectSumEsa.dsCore_dense
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T23:00:23.525974+00:00
-- url     : https://prove2.me/theorems/687e72b4-db4e-4887-a6a7-65c0bec2300e
-- title:
--   `BookProof.DirectSumEsa.dsCore_dense` (hD : ∀ i, Dense ((D i : Submodule ℂ (G i)) : Set (G i))) : Dense ((dsCore D : Submodule ℂ (lp G 2)) : Set (lp G 2))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDirectSumEsa`.
--
--   `BookProof.DirectSumEsa.dsCore_dense` (hD : ∀ i, Dense ((D i : Submodule ℂ (G i)) : Set (G i))) : Dense ((dsCore D : Submodule ℂ (lp G 2)) : Set (lp G 2))
--
--   Formalization note: Lean 4 identifier `BookProof.DirectSumEsa.dsCore_dense`.

-- Generated from ChapterDirectSumEsa.lean — theorem BookProof.DirectSumEsa.dsCore_dense
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

theorem BookProof.DirectSumEsa.dsCore_dense (hD : ∀ i, Dense ((D i : Submodule ℂ (G i)) : Set (G i))) :
    Dense ((dsCore D : Submodule ℂ (lp G 2)) : Set (lp G 2)) := by sorry

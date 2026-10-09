-- Prove2me | Theorems.Thm_BookProof_DirectSumEsa_mem_dsCore
-- name    : BookProof.DirectSumEsa.mem_dsCore
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:58:33.51582+00:00
-- url     : https://prove2.me/theorems/da4d68b4-2905-447d-ae45-774df5d64f9d
-- title:
--   `BookProof.DirectSumEsa.mem_dsCore` {D : ∀ i, Submodule ℂ (G i)} {f : lp G 2} : f ∈ dsCore D ↔ {i | (f : ∀ i, G i) i ≠ 0}.Finite ∧ ∀ i, (f : ∀ i, G i) i ∈ D i
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDirectSumEsa`.
--
--   `BookProof.DirectSumEsa.mem_dsCore` {D : ∀ i, Submodule ℂ (G i)} {f : lp G 2} : f ∈ dsCore D ↔ {i | (f : ∀ i, G i) i ≠ 0}.Finite ∧ ∀ i, (f : ∀ i, G i) i ∈ D i
--
--   Formalization note: Lean 4 identifier `BookProof.DirectSumEsa.mem_dsCore`.

-- Generated from ChapterDirectSumEsa.lean — theorem BookProof.DirectSumEsa.mem_dsCore
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterDirectSumEsa
open BookProof.DirectSumEsa


open scoped ENNReal


open BookProof.FarisLavine

noncomputable section

variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)]

theorem BookProof.DirectSumEsa.mem_dsCore {D : ∀ i, Submodule ℂ (G i)} {f : lp G 2} :
    f ∈ dsCore D ↔ {i | (f : ∀ i, G i) i ≠ 0}.Finite ∧ ∀ i, (f : ∀ i, G i) i ∈ D i := by sorry

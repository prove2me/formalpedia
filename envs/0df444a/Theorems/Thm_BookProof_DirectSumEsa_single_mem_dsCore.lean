-- Prove2me | Theorems.Thm_BookProof_DirectSumEsa_single_mem_dsCore
-- name    : BookProof.DirectSumEsa.single_mem_dsCore
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T10:11:56.405029+00:00
-- url     : https://prove2.me/theorems/62259f06-fe7d-4005-94c5-c4dbfbd2fd67
-- title:
--   `BookProof.DirectSumEsa.single_mem_dsCore` [DecidableEq ι] (i : ι) (u : D i) : (lp.single 2 i ((u : G i)) : lp G 2) ∈ dsCore D
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDirectSumEsa`.
--
--   `BookProof.DirectSumEsa.single_mem_dsCore` [DecidableEq ι] (i : ι) (u : D i) : (lp.single 2 i ((u : G i)) : lp G 2) ∈ dsCore D
--
--   Formalization note: Lean 4 identifier `BookProof.DirectSumEsa.single_mem_dsCore`.

-- Generated from ChapterDirectSumEsa.lean — theorem BookProof.DirectSumEsa.single_mem_dsCore
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

theorem BookProof.DirectSumEsa.single_mem_dsCore [DecidableEq ι] (i : ι) (u : D i) :
    (lp.single 2 i ((u : G i)) : lp G 2) ∈ dsCore D := by sorry

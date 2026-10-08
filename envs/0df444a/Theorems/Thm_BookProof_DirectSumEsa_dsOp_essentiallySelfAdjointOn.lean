-- Prove2me | Theorems.Thm_BookProof_DirectSumEsa_dsOp_essentiallySelfAdjointOn
-- name    : BookProof.DirectSumEsa.dsOp_essentiallySelfAdjointOn
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:59:11.249472+00:00
-- url     : https://prove2.me/theorems/8774e01f-0c98-4b04-af70-087df10c8989
-- title:
--   `BookProof.DirectSumEsa.dsOp_essentiallySelfAdjointOn` (H : ∀ i, D i →ₗ[ℂ] G i) (h : ∀ i, EssentiallySelfAdjointOn (D i) (H i)) : EssentiallySelfAdjointOn (dsCore D) (dsOp H)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDirectSumEsa`.
--
--   `BookProof.DirectSumEsa.dsOp_essentiallySelfAdjointOn` (H : ∀ i, D i →ₗ[ℂ] G i) (h : ∀ i, EssentiallySelfAdjointOn (D i) (H i)) : EssentiallySelfAdjointOn (dsCore D) (dsOp H)
--
--   Formalization note: Lean 4 identifier `BookProof.DirectSumEsa.dsOp_essentiallySelfAdjointOn`.

-- Generated from ChapterDirectSumEsa.lean — theorem BookProof.DirectSumEsa.dsOp_essentiallySelfAdjointOn
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

theorem BookProof.DirectSumEsa.dsOp_essentiallySelfAdjointOn (H : ∀ i, D i →ₗ[ℂ] G i)
    (h : ∀ i, EssentiallySelfAdjointOn (D i) (H i)) :
    EssentiallySelfAdjointOn (dsCore D) (dsOp H) := by sorry

-- Prove2me | Theorems.Thm_BookProof_DirectSumEsa_fockH_essentiallySelfAdjointOn
-- name    : BookProof.DirectSumEsa.fockH_essentiallySelfAdjointOn
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T23:00:48.789519+00:00
-- url     : https://prove2.me/theorems/bafa25d1-c5c2-43cc-a495-7ad06b858937
-- title:
--   `BookProof.DirectSumEsa.fockH_essentiallySelfAdjointOn` {w : ℝ → ℝ} (hw : Measurable w) : EssentiallySelfAdjointOn (fockCore w) ((fockCore w).subtype.comp (fockH hw))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDirectSumEsa`.
--
--   `BookProof.DirectSumEsa.fockH_essentiallySelfAdjointOn` {w : ℝ → ℝ} (hw : Measurable w) : EssentiallySelfAdjointOn (fockCore w) ((fockCore w).subtype.comp (fockH hw))
--
--   Formalization note: Lean 4 identifier `BookProof.DirectSumEsa.fockH_essentiallySelfAdjointOn`.

-- Generated from ChapterDirectSumEsa.lean — theorem BookProof.DirectSumEsa.fockH_essentiallySelfAdjointOn
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
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.DirectSumEsa.fockH_essentiallySelfAdjointOn {w : ℝ → ℝ} (hw : Measurable w) :
    EssentiallySelfAdjointOn (fockCore w) ((fockCore w).subtype.comp (fockH hw)) := by sorry

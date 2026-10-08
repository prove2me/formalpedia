-- Prove2me | Theorems.Thm_BookProof_DirectSumEsa_essentiallySelfAdjointOn_of_hasZeroDeficiencyOn
-- name    : BookProof.DirectSumEsa.essentiallySelfAdjointOn_of_hasZeroDeficiencyOn
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:59:26.356448+00:00
-- url     : https://prove2.me/theorems/9cb613fd-82ae-433f-ab14-33be1cf28dd5
-- title:
--   `BookProof.DirectSumEsa.essentiallySelfAdjointOn_of_hasZeroDeficiencyOn` {Dom : Submodule ℂ F} (A : Dom →ₗ[ℂ] Dom) (h : HasZeroDeficiencyOn Dom A) : EssentiallySelfAdjointOn Dom (D
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDirectSumEsa`.
--
--   `BookProof.DirectSumEsa.essentiallySelfAdjointOn_of_hasZeroDeficiencyOn` {Dom : Submodule ℂ F} (A : Dom →ₗ[ℂ] Dom) (h : HasZeroDeficiencyOn Dom A) : EssentiallySelfAdjointOn Dom (Dom.subtype.comp A)
--
--   Formalization note: Lean 4 identifier `BookProof.DirectSumEsa.essentiallySelfAdjointOn_of_hasZeroDeficiencyOn`.

-- Generated from ChapterDirectSumEsa.lean — theorem BookProof.DirectSumEsa.essentiallySelfAdjointOn_of_hasZeroDeficiencyOn
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesFlow
open BookProof.DirectSumEsa


open scoped ENNReal


open BookProof.FarisLavine

noncomputable section

variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)]

variable {D : ∀ i, Submodule ℂ (G i)}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
open BookProof.NavierStokesFlow

theorem BookProof.DirectSumEsa.essentiallySelfAdjointOn_of_hasZeroDeficiencyOn {Dom : Submodule ℂ F}
    (A : Dom →ₗ[ℂ] Dom) (h : HasZeroDeficiencyOn Dom A) :
    EssentiallySelfAdjointOn Dom (Dom.subtype.comp A) := by sorry

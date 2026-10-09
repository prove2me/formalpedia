-- Prove2me | Theorems.Thm_BookProof_DirectSumEsa_hasZeroDeficiencyOn_of_essentiallySelfAdjointOn
-- name    : BookProof.DirectSumEsa.hasZeroDeficiencyOn_of_essentiallySelfAdjointOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T23:03:04.15269+00:00
-- url     : https://prove2.me/theorems/b7e57868-49b4-49f3-aac1-fddd5d003928
-- title:
--   `BookProof.DirectSumEsa.hasZeroDeficiencyOn_of_essentiallySelfAdjointOn` {Dom : Submodule ℂ F} (A : Dom →ₗ[ℂ] Dom) (h : EssentiallySelfAdjointOn Dom (Dom.subtype.comp A)) : HasZero
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDirectSumEsa`.
--
--   `BookProof.DirectSumEsa.hasZeroDeficiencyOn_of_essentiallySelfAdjointOn` {Dom : Submodule ℂ F} (A : Dom →ₗ[ℂ] Dom) (h : EssentiallySelfAdjointOn Dom (Dom.subtype.comp A)) : HasZeroDeficiencyOn Dom A
--
--   Formalization note: Lean 4 identifier `BookProof.DirectSumEsa.hasZeroDeficiencyOn_of_essentiallySelfAdjointOn`.

-- Generated from ChapterDirectSumEsa.lean — theorem BookProof.DirectSumEsa.hasZeroDeficiencyOn_of_essentiallySelfAdjointOn
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

theorem BookProof.DirectSumEsa.hasZeroDeficiencyOn_of_essentiallySelfAdjointOn {Dom : Submodule ℂ F}
    (A : Dom →ₗ[ℂ] Dom) (h : EssentiallySelfAdjointOn Dom (Dom.subtype.comp A)) :
    HasZeroDeficiencyOn Dom A := by sorry

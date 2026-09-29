-- Prove2me | Theorems.Thm_BookProof_ChapterSirkGramWhitening_synthesis_injective_of_linearIndependent
-- name    : BookProof.ChapterSirkGramWhitening.synthesis_injective_of_linearIndependent
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T05:30:26.190136+00:00
-- url     : https://prove2.me/theorems/b02fb6ec-3e7a-4bf9-a525-eb533509334d
-- title:
--   {m : ℕ} {w : Fin m → E} (hw : LinearIndependent ℂ w) : Function.Injective (synthesis w)
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkGramWhitening.synthesis_injective_of_linearIndependent` (module `BookProof.ChapterSirkGramWhitening`), source chapter `BookProof/ChapterChapterSirkGramWhitening.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkGramWhitening.lean

-- Generated from ChapterSirkGramWhitening.lean — theorem BookProof.ChapterSirkGramWhitening.synthesis_injective_of_linearIndependent
import Mathlib
import Definitions.Def_ChapterSirkGramWhitening
open BookProof.ChapterSirkGramWhitening








noncomputable section


open scoped InnerProductSpace
open Matrix
open BookProof.ChapterH4 BookProof.ChapterSirkWhitening

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.ChapterSirkGramWhitening.synthesis_injective_of_linearIndependent {m : ℕ} {w : Fin m → E}
    (hw : LinearIndependent ℂ w) : Function.Injective (synthesis w) := by sorry

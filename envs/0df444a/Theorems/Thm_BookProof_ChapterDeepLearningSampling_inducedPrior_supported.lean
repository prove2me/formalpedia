-- Prove2me | Theorems.Thm_BookProof_ChapterDeepLearningSampling_inducedPrior_supported
-- name    : BookProof.ChapterDeepLearningSampling.inducedPrior_supported
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:28:58.895288+00:00
-- url     : https://prove2.me/theorems/86553c5e-f3a8-41de-bf59-bde60f701064
-- title:
--   `BookProof.ChapterDeepLearningSampling.inducedPrior_supported` (seedProb : Seed → ℝ) (train : Seed → Model) (admissible : Model → Prop) (htrain : ∀ s, admissible (train s)) {m : Mo
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDeepLearningSampling`.
--
--   `BookProof.ChapterDeepLearningSampling.inducedPrior_supported` (seedProb : Seed → ℝ) (train : Seed → Model) (admissible : Model → Prop) (htrain : ∀ s, admissible (train s)) {m : Model} (hm : ¬ admissible m) : inducedPrior seedProb train m = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterDeepLearningSampling.inducedPrior_supported`.

-- Generated from ChapterDeepLearningSampling.lean — theorem BookProof.ChapterDeepLearningSampling.inducedPrior_supported
import Mathlib
import Definitions.Def_ChapterDeepLearningSampling
open BookProof.ChapterDeepLearningSampling


open scoped BigOperators


variable {Seed Model Data : Type*}
variable [Fintype Seed] [DecidableEq Model]

theorem BookProof.ChapterDeepLearningSampling.inducedPrior_supported (seedProb : Seed → ℝ) (train : Seed → Model)
    (admissible : Model → Prop)
    (htrain : ∀ s, admissible (train s)) {m : Model} (hm : ¬ admissible m) :
    inducedPrior seedProb train m = 0 := by sorry

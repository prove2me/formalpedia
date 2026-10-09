-- Prove2me | Theorems.Thm_BookProof_ChapterGaugeIncompleteFixing_remnant_faithful
-- name    : BookProof.ChapterGaugeIncompleteFixing.remnant_faithful
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T11:11:56.27298+00:00
-- url     : https://prove2.me/theorems/0a43f84b-9da3-431c-8055-0031fb9e748c
-- title:
--   `BookProof.ChapterGaugeIncompleteFixing.remnant_faithful` [Nonempty X] (h : MovesEveryPointOfSpectrum G X) {g : G} (hg : ∀ x : X, g • x = x) : g = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGaugeIncompleteFixing`.
--
--   `BookProof.ChapterGaugeIncompleteFixing.remnant_faithful` [Nonempty X] (h : MovesEveryPointOfSpectrum G X) {g : G} (hg : ∀ x : X, g • x = x) : g = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGaugeIncompleteFixing.remnant_faithful`.

-- Generated from ChapterGaugeIncompleteFixing.lean — theorem BookProof.ChapterGaugeIncompleteFixing.remnant_faithful
import Mathlib
import Definitions.Def_ChapterGaugeIncompleteFixing
open BookProof.ChapterGaugeIncompleteFixing


open scoped InnerProductSpace

variable {X : Type*}
variable (G : Type*) [Group G] [MulAction G X]

theorem BookProof.ChapterGaugeIncompleteFixing.remnant_faithful [Nonempty X] (h : MovesEveryPointOfSpectrum G X)
    {g : G} (hg : ∀ x : X, g • x = x) : g = 1 := by sorry

-- Prove2me | Theorems.Thm_BookProof_ChapterGaugeIncompleteFixing_unconstrained_gauge_fixing_incomplete
-- name    : BookProof.ChapterGaugeIncompleteFixing.unconstrained_gauge_fixing_incomplete
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T11:11:59.761229+00:00
-- url     : https://prove2.me/theorems/eb4419b7-1cd5-4f5c-84fa-ed65dd26965e
-- title:
--   `BookProof.ChapterGaugeIncompleteFixing.unconstrained_gauge_fixing_incomplete` [Nontrivial G] [Nonempty X] (h : MovesEveryPointOfSpectrum G X) : ¬ IsCompleteGaugeFixing' G (Set.uni
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGaugeIncompleteFixing`.
--
--   `BookProof.ChapterGaugeIncompleteFixing.unconstrained_gauge_fixing_incomplete` [Nontrivial G] [Nonempty X] (h : MovesEveryPointOfSpectrum G X) : ¬ IsCompleteGaugeFixing' G (Set.univ : Set X)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGaugeIncompleteFixing.unconstrained_gauge_fixing_incomplete`.

-- Generated from ChapterGaugeIncompleteFixing.lean — theorem BookProof.ChapterGaugeIncompleteFixing.unconstrained_gauge_fixing_incomplete
import Mathlib
import Definitions.Def_ChapterGaugeIncompleteFixing
open BookProof.ChapterGaugeIncompleteFixing


open scoped InnerProductSpace

variable {X : Type*}
variable (G : Type*) [Group G] [MulAction G X]

theorem BookProof.ChapterGaugeIncompleteFixing.unconstrained_gauge_fixing_incomplete [Nontrivial G] [Nonempty X]
    (h : MovesEveryPointOfSpectrum G X) :
    ¬ IsCompleteGaugeFixing' G (Set.univ : Set X) := by sorry

-- Prove2me | Theorems.Thm_BookProof_ChapterGaugeComprehensiveFixing_not_isPhysicalObservable_indicator
-- name    : BookProof.ChapterGaugeComprehensiveFixing.not_isPhysicalObservable_indicator
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T10:57:26.18637+00:00
-- url     : https://prove2.me/theorems/87bd2327-9e13-4a7c-a849-89185dcc5126
-- title:
--   `BookProof.ChapterGaugeComprehensiveFixing.not_isPhysicalObservable_indicator` [Nontrivial G] [Nonempty X] (hcomp : IsComprehensiveGaugeFixing G S) (hcompl : IsCompleteGaugeFixing'
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGaugeComprehensiveFixing`.
--
--   `BookProof.ChapterGaugeComprehensiveFixing.not_isPhysicalObservable_indicator` [Nontrivial G] [Nonempty X] (hcomp : IsComprehensiveGaugeFixing G S) (hcompl : IsCompleteGaugeFixing' G S) (hfree : MovesEveryPointOfSpectrum G X) : ¬ IsPhysicalObservable G (S.indicator (fun _ => (1 : ℝ)))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGaugeComprehensiveFixing.not_isPhysicalObservable_indicator`.

-- Generated from ChapterGaugeComprehensiveFixing.lean — theorem BookProof.ChapterGaugeComprehensiveFixing.not_isPhysicalObservable_indicator
import Mathlib
import Definitions.Def_ChapterGaugeComprehensiveFixing
import Definitions.Def_ChapterGaugeIncompleteFixing
open BookProof.ChapterGaugeIncompleteFixing
open BookProof.ChapterGaugeComprehensiveFixing



open BookProof.ChapterGaugeIncompleteFixing

variable {X : Type*} (G : Type*) [Group G] [MulAction G X]
variable {X : Type*} {G : Type*} [Group G] [MulAction G X] {S : Set X}

theorem BookProof.ChapterGaugeComprehensiveFixing.not_isPhysicalObservable_indicator [Nontrivial G] [Nonempty X]
    (hcomp : IsComprehensiveGaugeFixing G S) (hcompl : IsCompleteGaugeFixing' G S)
    (hfree : MovesEveryPointOfSpectrum G X) :
    ¬ IsPhysicalObservable G (S.indicator (fun _ => (1 : ℝ))) := by sorry

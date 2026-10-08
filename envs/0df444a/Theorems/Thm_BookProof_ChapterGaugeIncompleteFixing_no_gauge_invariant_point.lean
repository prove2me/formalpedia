-- Prove2me | Theorems.Thm_BookProof_ChapterGaugeIncompleteFixing_no_gauge_invariant_point
-- name    : BookProof.ChapterGaugeIncompleteFixing.no_gauge_invariant_point
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T11:12:03.263883+00:00
-- url     : https://prove2.me/theorems/955282f7-7b63-463c-ac7f-8a92d1c04a24
-- title:
--   `BookProof.ChapterGaugeIncompleteFixing.no_gauge_invariant_point` [Nontrivial G] (h : MovesEveryPointOfSpectrum G X) (x : X) : ∃ g : G, g • x ≠ x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGaugeIncompleteFixing`.
--
--   `BookProof.ChapterGaugeIncompleteFixing.no_gauge_invariant_point` [Nontrivial G] (h : MovesEveryPointOfSpectrum G X) (x : X) : ∃ g : G, g • x ≠ x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGaugeIncompleteFixing.no_gauge_invariant_point`.

-- Generated from ChapterGaugeIncompleteFixing.lean — theorem BookProof.ChapterGaugeIncompleteFixing.no_gauge_invariant_point
import Mathlib
import Definitions.Def_ChapterGaugeIncompleteFixing
open BookProof.ChapterGaugeIncompleteFixing


open scoped InnerProductSpace

variable {X : Type*}
variable (G : Type*) [Group G] [MulAction G X]

theorem BookProof.ChapterGaugeIncompleteFixing.no_gauge_invariant_point [Nontrivial G] (h : MovesEveryPointOfSpectrum G X)
    (x : X) : ∃ g : G, g • x ≠ x := by sorry

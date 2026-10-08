-- Prove2me | Theorems.Thm_BookProof_ChapterGaugeUnconstrainedSpectrum_exists_isUnconstrainedGaugeFixing
-- name    : BookProof.ChapterGaugeUnconstrainedSpectrum.exists_isUnconstrainedGaugeFixing
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T12:16:28.755457+00:00
-- url     : https://prove2.me/theorems/92c8a861-5d53-4d12-8adf-4173d610eff4
-- title:
--   `BookProof.ChapterGaugeUnconstrainedSpectrum.exists_isUnconstrainedGaugeFixing` : ∃ (G : Type) (_ : Group G) (X : Type) (U : G → Op X), Nontrivial G ∧ IsUnconstrainedGaugeFixing U
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGaugeUnconstrainedSpectrum`.
--
--   `BookProof.ChapterGaugeUnconstrainedSpectrum.exists_isUnconstrainedGaugeFixing` : ∃ (G : Type) (_ : Group G) (X : Type) (U : G → Op X), Nontrivial G ∧ IsUnconstrainedGaugeFixing U ∧ constrainedSpectrum U = Set.univ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGaugeUnconstrainedSpectrum.exists_isUnconstrainedGaugeFixing`.

-- Generated from ChapterGaugeUnconstrainedSpectrum.lean — theorem BookProof.ChapterGaugeUnconstrainedSpectrum.exists_isUnconstrainedGaugeFixing
import Mathlib
import Definitions.Def_ChapterGaugeUnconstrainedSpectrum
open BookProof.ChapterGaugeUnconstrainedSpectrum



variable {X : Type*}

variable {G : Type*} [Group G]

theorem BookProof.ChapterGaugeUnconstrainedSpectrum.exists_isUnconstrainedGaugeFixing :
    ∃ (G : Type) (_ : Group G) (X : Type) (U : G → Op X),
      Nontrivial G ∧ IsUnconstrainedGaugeFixing U ∧
        constrainedSpectrum U = Set.univ := by sorry

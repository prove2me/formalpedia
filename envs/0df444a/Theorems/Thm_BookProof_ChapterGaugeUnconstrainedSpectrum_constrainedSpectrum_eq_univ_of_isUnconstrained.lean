-- Prove2me | Theorems.Thm_BookProof_ChapterGaugeUnconstrainedSpectrum_constrainedSpectrum_eq_univ_of_isUnconstrained
-- name    : BookProof.ChapterGaugeUnconstrainedSpectrum.constrainedSpectrum_eq_univ_of_isUnconstrained
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T12:15:44.290719+00:00
-- url     : https://prove2.me/theorems/f69ddd33-2387-4bfc-823a-c88321a32980
-- title:
--   `BookProof.ChapterGaugeUnconstrainedSpectrum.constrainedSpectrum_eq_univ_of_isUnconstrained` {U : G → Op X} (hU : IsUnconstrainedGaugeFixing U) (hU1 : U 1 = LinearMap.id) : constra
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGaugeUnconstrainedSpectrum`.
--
--   `BookProof.ChapterGaugeUnconstrainedSpectrum.constrainedSpectrum_eq_univ_of_isUnconstrained` {U : G → Op X} (hU : IsUnconstrainedGaugeFixing U) (hU1 : U 1 = LinearMap.id) : constrainedSpectrum U = Set.univ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGaugeUnconstrainedSpectrum.constrainedSpectrum_eq_univ_of_isUnconstrained`.

-- Generated from ChapterGaugeUnconstrainedSpectrum.lean — theorem BookProof.ChapterGaugeUnconstrainedSpectrum.constrainedSpectrum_eq_univ_of_isUnconstrained
import Mathlib
import Definitions.Def_ChapterGaugeUnconstrainedSpectrum
import Definitions.Def_ChapterAbelianDiagonalCountable
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.ChapterGaugeUnconstrainedSpectrum



variable {X : Type*}

variable {G : Type*} [Group G]

theorem BookProof.ChapterGaugeUnconstrainedSpectrum.constrainedSpectrum_eq_univ_of_isUnconstrained {U : G → Op X}
    (hU : IsUnconstrainedGaugeFixing U) (hU1 : U 1 = LinearMap.id) :
    constrainedSpectrum U = Set.univ := by sorry

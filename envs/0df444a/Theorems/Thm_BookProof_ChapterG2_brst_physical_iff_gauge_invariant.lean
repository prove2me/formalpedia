-- Prove2me | Theorems.Thm_BookProof_ChapterG2_brst_physical_iff_gauge_invariant
-- name    : BookProof.ChapterG2.brst_physical_iff_gauge_invariant
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T10:50:39.386754+00:00
-- url     : https://prove2.me/theorems/e357311d-f469-45fa-a838-43c7657f2506
-- title:
--   `BookProof.ChapterG2.brst_physical_iff_gauge_invariant` (a : A) : (![a, 0] ∈ brstKer Q) ↔ Q * a = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterG2`.
--
--   `BookProof.ChapterG2.brst_physical_iff_gauge_invariant` (a : A) : (![a, 0] ∈ brstKer Q) ↔ Q * a = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterG2.brst_physical_iff_gauge_invariant`.

-- Generated from ChapterG2.lean — theorem BookProof.ChapterG2.brst_physical_iff_gauge_invariant
import Mathlib
import Definitions.Def_ChapterG2
open BookProof.ChapterG2


open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]
variable {A : Type*} [CommRing A] (Q : A)

theorem BookProof.ChapterG2.brst_physical_iff_gauge_invariant (a : A) :
    (![a, 0] ∈ brstKer Q) ↔ Q * a = 0 := by sorry

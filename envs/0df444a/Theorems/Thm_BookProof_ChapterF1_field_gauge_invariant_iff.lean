-- Prove2me | Theorems.Thm_BookProof_ChapterF1_field_gauge_invariant_iff
-- name    : BookProof.ChapterF1.field_gauge_invariant_iff
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T03:46:11.216658+00:00
-- url     : https://prove2.me/theorems/16dd7437-92cf-4326-996a-942b6a98ee9f
-- title:
--   `BookProof.ChapterF1.field_gauge_invariant_iff` (Q : ℂ[X]) (a : ℂ[X]) : (![a, 0] ∈ BookProof.ChapterG2.brstKer Q) ↔ Q * a = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF1`.
--
--   `BookProof.ChapterF1.field_gauge_invariant_iff` (Q : ℂ[X]) (a : ℂ[X]) : (![a, 0] ∈ BookProof.ChapterG2.brstKer Q) ↔ Q * a = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF1.field_gauge_invariant_iff`.

-- Generated from ChapterF1.lean — theorem BookProof.ChapterF1.field_gauge_invariant_iff
import Mathlib
import Definitions.Def_ChapterF1
open BookProof.ChapterF1


open Polynomial Finset
open scoped BigOperators


noncomputable section

theorem BookProof.ChapterF1.field_gauge_invariant_iff (Q : ℂ[X]) (a : ℂ[X]) :
    (![a, 0] ∈ BookProof.ChapterG2.brstKer Q) ↔ Q * a = 0 := by sorry

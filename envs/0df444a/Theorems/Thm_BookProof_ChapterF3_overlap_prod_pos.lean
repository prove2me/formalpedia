-- Prove2me | Theorems.Thm_BookProof_ChapterF3_overlap_prod_pos
-- name    : BookProof.ChapterF3.overlap_prod_pos
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T03:49:12.164595+00:00
-- url     : https://prove2.me/theorems/f0b7ffc1-87ec-49f2-93e2-84484d96fd08
-- title:
--   `BookProof.ChapterF3.overlap_prod_pos` {ι : Type*} (s : Finset ι) (w : ι → ℝ) (hw : ∀ i ∈ s, 0 < w i) : 0 < ∏ i ∈ s, Real.sqrt (w i / (2 * Real.pi))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF3`.
--
--   `BookProof.ChapterF3.overlap_prod_pos` {ι : Type*} (s : Finset ι) (w : ι → ℝ) (hw : ∀ i ∈ s, 0 < w i) : 0 < ∏ i ∈ s, Real.sqrt (w i / (2 * Real.pi))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF3.overlap_prod_pos`.

-- Generated from ChapterF3.lean — theorem BookProof.ChapterF3.overlap_prod_pos
import Mathlib
import Definitions.Def_ChapterF3
open BookProof.ChapterF3


open scoped BigOperators
open Polynomial


noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem BookProof.ChapterF3.overlap_prod_pos {ι : Type*} (s : Finset ι) (w : ι → ℝ) (hw : ∀ i ∈ s, 0 < w i) :
    0 < ∏ i ∈ s, Real.sqrt (w i / (2 * Real.pi)) := by sorry

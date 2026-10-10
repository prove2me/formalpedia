-- Prove2me | Theorems.Thm_BookProof_ChapterMaxEntropy_negMulLog_sub_le
-- name    : BookProof.ChapterMaxEntropy.negMulLog_sub_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T13:00:05.715984+00:00
-- url     : https://prove2.me/theorems/d1da988f-9d1a-421f-9b98-4a35a56df985
-- title:
--   `BookProof.ChapterMaxEntropy.negMulLog_sub_le` (n : ℕ) (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) : Real.negMulLog x - x * Real.log n ≤ (n : ℝ)⁻¹ - x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMaxEntropy`.
--
--   `BookProof.ChapterMaxEntropy.negMulLog_sub_le` (n : ℕ) (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) : Real.negMulLog x - x * Real.log n ≤ (n : ℝ)⁻¹ - x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMaxEntropy.negMulLog_sub_le`.

-- Generated from ChapterMaxEntropy.lean — theorem BookProof.ChapterMaxEntropy.negMulLog_sub_le
import Mathlib
import Definitions.Def_ChapterMaxEntropy
open BookProof.ChapterMaxEntropy


open Real BigOperators Finset


variable {α : Type*} [Fintype α]

theorem BookProof.ChapterMaxEntropy.negMulLog_sub_le (n : ℕ) (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    Real.negMulLog x - x * Real.log n ≤ (n : ℝ)⁻¹ - x := by sorry

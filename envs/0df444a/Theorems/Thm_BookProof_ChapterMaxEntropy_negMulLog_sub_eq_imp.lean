-- Prove2me | Theorems.Thm_BookProof_ChapterMaxEntropy_negMulLog_sub_eq_imp
-- name    : BookProof.ChapterMaxEntropy.negMulLog_sub_eq_imp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T13:00:53.81463+00:00
-- url     : https://prove2.me/theorems/af0ec57e-1bda-40de-9eb5-d74ee20c4294
-- title:
--   `BookProof.ChapterMaxEntropy.negMulLog_sub_eq_imp` (n : ℕ) (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) (heq : Real.negMulLog x - x * Real.log n = (n : ℝ)⁻¹ - x) : x = (n : ℝ)⁻¹
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMaxEntropy`.
--
--   `BookProof.ChapterMaxEntropy.negMulLog_sub_eq_imp` (n : ℕ) (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) (heq : Real.negMulLog x - x * Real.log n = (n : ℝ)⁻¹ - x) : x = (n : ℝ)⁻¹
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMaxEntropy.negMulLog_sub_eq_imp`.

-- Generated from ChapterMaxEntropy.lean — theorem BookProof.ChapterMaxEntropy.negMulLog_sub_eq_imp
import Mathlib
import Definitions.Def_ChapterMaxEntropy
open BookProof.ChapterMaxEntropy


open Real BigOperators Finset


variable {α : Type*} [Fintype α]

theorem BookProof.ChapterMaxEntropy.negMulLog_sub_eq_imp (n : ℕ) (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x)
    (heq : Real.negMulLog x - x * Real.log n = (n : ℝ)⁻¹ - x) : x = (n : ℝ)⁻¹ := by sorry

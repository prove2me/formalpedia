-- Prove2me | Theorems.Thm_BookProof_WeakSecondDeriv_deriv_eq_zero_out
-- name    : BookProof.WeakSecondDeriv.deriv_eq_zero_out
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:10:12.934984+00:00
-- url     : https://prove2.me/theorems/33fc7c87-b609-40f7-8daa-b23c024d2c8a
-- title:
--   `BookProof.WeakSecondDeriv.deriv_eq_zero_out` {g : ℝ → ℝ} {R : ℝ} (hsupp : tsupport g ⊆ Icc (-R) R) {x : ℝ} (hx : x ∉ Icc (-R) R) : deriv g x = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeakSecondDerivative`.
--
--   `BookProof.WeakSecondDeriv.deriv_eq_zero_out` {g : ℝ → ℝ} {R : ℝ} (hsupp : tsupport g ⊆ Icc (-R) R) {x : ℝ} (hx : x ∉ Icc (-R) R) : deriv g x = 0
--
--   Formalization note: Lean 4 identifier `BookProof.WeakSecondDeriv.deriv_eq_zero_out`.

-- Generated from ChapterWeakSecondDerivative.lean — theorem BookProof.WeakSecondDeriv.deriv_eq_zero_out
import Mathlib
import Definitions.Def_ChapterWeakSecondDerivative
open BookProof.WeakSecondDeriv



open MeasureTheory Filter Topology intervalIntegral Set

noncomputable section

theorem BookProof.WeakSecondDeriv.deriv_eq_zero_out {g : ℝ → ℝ} {R : ℝ} (hsupp : tsupport g ⊆ Icc (-R) R)
    {x : ℝ} (hx : x ∉ Icc (-R) R) : deriv g x = 0 := by sorry

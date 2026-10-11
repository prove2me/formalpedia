-- Prove2me | Theorems.Thm_BookProof_WeakSecondDeriv_integral_eq_intervalIntegral
-- name    : BookProof.WeakSecondDeriv.integral_eq_intervalIntegral
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:10:32.783269+00:00
-- url     : https://prove2.me/theorems/40fdcdfc-aed0-4e6b-95a3-e3af602e812c
-- title:
--   `BookProof.WeakSecondDeriv.integral_eq_intervalIntegral` {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℝ → F} {R a b : ℝ} (hR : 0 ≤ R) (hf : ∀ x, x ∉ Icc (-R) R → f x =
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeakSecondDerivative`.
--
--   `BookProof.WeakSecondDeriv.integral_eq_intervalIntegral` {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℝ → F} {R a b : ℝ} (hR : 0 ≤ R) (hf : ∀ x, x ∉ Icc (-R) R → f x = 0) (ha : a < -R) (hb : R < b) : ∫ x, f x = ∫ x in a..b, f x
--
--   Formalization note: Lean 4 identifier `BookProof.WeakSecondDeriv.integral_eq_intervalIntegral`.

-- Generated from ChapterWeakSecondDerivative.lean — theorem BookProof.WeakSecondDeriv.integral_eq_intervalIntegral
import Mathlib
import Definitions.Def_ChapterWeakSecondDerivative
open BookProof.WeakSecondDeriv



open MeasureTheory Filter Topology intervalIntegral Set

noncomputable section

theorem BookProof.WeakSecondDeriv.integral_eq_intervalIntegral {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} {R a b : ℝ} (hR : 0 ≤ R)
    (hf : ∀ x, x ∉ Icc (-R) R → f x = 0) (ha : a < -R) (hb : R < b) :
    ∫ x, f x = ∫ x in a..b, f x := by sorry

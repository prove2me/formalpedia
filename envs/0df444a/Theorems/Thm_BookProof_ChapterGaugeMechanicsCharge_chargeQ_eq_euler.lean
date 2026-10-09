-- Prove2me | Theorems.Thm_BookProof_ChapterGaugeMechanicsCharge_chargeQ_eq_euler
-- name    : BookProof.ChapterGaugeMechanicsCharge.chargeQ_eq_euler
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T11:14:49.196285+00:00
-- url     : https://prove2.me/theorems/eafaddee-b582-49d3-8fd2-d9f4c528061c
-- title:
--   `BookProof.ChapterGaugeMechanicsCharge.chargeQ_eq_euler` (p : P) : chargeQ p = (-Complex.I) • (eulerOp p + (2 : ℂ) • p)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGaugeMechanicsCharge`.
--
--   `BookProof.ChapterGaugeMechanicsCharge.chargeQ_eq_euler` (p : P) : chargeQ p = (-Complex.I) • (eulerOp p + (2 : ℂ) • p)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGaugeMechanicsCharge.chargeQ_eq_euler`.

-- Generated from ChapterGaugeMechanicsCharge.lean — theorem BookProof.ChapterGaugeMechanicsCharge.chargeQ_eq_euler
import Mathlib
import Definitions.Def_ChapterGaugeMechanicsCharge
open BookProof.ChapterGaugeMechanicsCharge




open MvPolynomial

theorem BookProof.ChapterGaugeMechanicsCharge.chargeQ_eq_euler (p : P) :
    chargeQ p = (-Complex.I) • (eulerOp p + (2 : ℂ) • p) := by sorry

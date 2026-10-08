-- Prove2me | Theorems.Thm_BookProof_ChapterGaugeMechanicsCharge_chargeQ_comm_mul
-- name    : BookProof.ChapterGaugeMechanicsCharge.chargeQ_comm_mul
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T11:15:45.369625+00:00
-- url     : https://prove2.me/theorems/4b1f8b49-9917-458f-a216-5f9be0e013fa
-- title:
--   `BookProof.ChapterGaugeMechanicsCharge.chargeQ_comm_mul` (g p : P) : chargeQ (g * p) - g * chargeQ p = (-Complex.I) • (eulerOp g * p)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGaugeMechanicsCharge`.
--
--   `BookProof.ChapterGaugeMechanicsCharge.chargeQ_comm_mul` (g p : P) : chargeQ (g * p) - g * chargeQ p = (-Complex.I) • (eulerOp g * p)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGaugeMechanicsCharge.chargeQ_comm_mul`.

-- Generated from ChapterGaugeMechanicsCharge.lean — theorem BookProof.ChapterGaugeMechanicsCharge.chargeQ_comm_mul
import Mathlib
import Definitions.Def_ChapterGaugeMechanicsCharge
open BookProof.ChapterGaugeMechanicsCharge




open MvPolynomial

theorem BookProof.ChapterGaugeMechanicsCharge.chargeQ_comm_mul (g p : P) :
    chargeQ (g * p) - g * chargeQ p = (-Complex.I) • (eulerOp g * p) := by sorry

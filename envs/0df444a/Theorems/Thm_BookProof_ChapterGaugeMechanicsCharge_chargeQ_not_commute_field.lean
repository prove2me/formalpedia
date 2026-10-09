-- Prove2me | Theorems.Thm_BookProof_ChapterGaugeMechanicsCharge_chargeQ_not_commute_field
-- name    : BookProof.ChapterGaugeMechanicsCharge.chargeQ_not_commute_field
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T11:14:28.703315+00:00
-- url     : https://prove2.me/theorems/6eb72853-b713-4bd9-9d7c-0304f126117f
-- title:
--   `BookProof.ChapterGaugeMechanicsCharge.chargeQ_not_commute_field` (j : Fin 2) (p : P) : chargeQ (X j * p) - X j * chargeQ p = (-Complex.I) • (X j * p)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGaugeMechanicsCharge`.
--
--   `BookProof.ChapterGaugeMechanicsCharge.chargeQ_not_commute_field` (j : Fin 2) (p : P) : chargeQ (X j * p) - X j * chargeQ p = (-Complex.I) • (X j * p)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGaugeMechanicsCharge.chargeQ_not_commute_field`.

-- Generated from ChapterGaugeMechanicsCharge.lean — theorem BookProof.ChapterGaugeMechanicsCharge.chargeQ_not_commute_field
import Mathlib
import Definitions.Def_ChapterGaugeMechanicsCharge
open BookProof.ChapterGaugeMechanicsCharge




open MvPolynomial

theorem BookProof.ChapterGaugeMechanicsCharge.chargeQ_not_commute_field (j : Fin 2) (p : P) :
    chargeQ (X j * p) - X j * chargeQ p = (-Complex.I) • (X j * p) := by sorry

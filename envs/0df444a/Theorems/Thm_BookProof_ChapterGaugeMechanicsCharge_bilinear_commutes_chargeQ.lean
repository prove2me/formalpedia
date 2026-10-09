-- Prove2me | Theorems.Thm_BookProof_ChapterGaugeMechanicsCharge_bilinear_commutes_chargeQ
-- name    : BookProof.ChapterGaugeMechanicsCharge.bilinear_commutes_chargeQ
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T11:15:48.418405+00:00
-- url     : https://prove2.me/theorems/8d2801af-bb70-4ae7-bda8-4d047218371b
-- title:
--   `BookProof.ChapterGaugeMechanicsCharge.bilinear_commutes_chargeQ` (j k : Fin 2) (p : P) : chargeQ (X j * pderiv k p) = X j * pderiv k (chargeQ p)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGaugeMechanicsCharge`.
--
--   `BookProof.ChapterGaugeMechanicsCharge.bilinear_commutes_chargeQ` (j k : Fin 2) (p : P) : chargeQ (X j * pderiv k p) = X j * pderiv k (chargeQ p)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGaugeMechanicsCharge.bilinear_commutes_chargeQ`.

-- Generated from ChapterGaugeMechanicsCharge.lean — theorem BookProof.ChapterGaugeMechanicsCharge.bilinear_commutes_chargeQ
import Mathlib
import Definitions.Def_ChapterGaugeMechanicsCharge
open BookProof.ChapterGaugeMechanicsCharge




open MvPolynomial

theorem BookProof.ChapterGaugeMechanicsCharge.bilinear_commutes_chargeQ (j k : Fin 2) (p : P) :
    chargeQ (X j * pderiv k p) = X j * pderiv k (chargeQ p) := by sorry

-- Prove2me | Theorems.Thm_BookProof_ChapterGaugeMechanicsCharge_pderiv_comm_core
-- name    : BookProof.ChapterGaugeMechanicsCharge.pderiv_comm_core
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T11:13:34.501946+00:00
-- url     : https://prove2.me/theorems/4352b18a-ebfc-417c-beb0-7831a7a9d60f
-- title:
--   `BookProof.ChapterGaugeMechanicsCharge.pderiv_comm_core` (j k : Fin 2) (p : P) : pderiv j (pderiv k p) = pderiv k (pderiv j p)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGaugeMechanicsCharge`.
--
--   `BookProof.ChapterGaugeMechanicsCharge.pderiv_comm_core` (j k : Fin 2) (p : P) : pderiv j (pderiv k p) = pderiv k (pderiv j p)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGaugeMechanicsCharge.pderiv_comm_core`.

-- Generated from ChapterGaugeMechanicsCharge.lean — theorem BookProof.ChapterGaugeMechanicsCharge.pderiv_comm_core
import Mathlib
import Definitions.Def_ChapterGaugeMechanicsCharge
open BookProof.ChapterGaugeMechanicsCharge




open MvPolynomial

theorem BookProof.ChapterGaugeMechanicsCharge.pderiv_comm_core (j k : Fin 2) (p : P) :
    pderiv j (pderiv k p) = pderiv k (pderiv j p) := by sorry

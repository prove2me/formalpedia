-- Prove2me | Theorems.Thm_BookProof_SmHiggsVacuum_higgsV_sq_form
-- name    : BookProof.SmHiggsVacuum.higgsV_sq_form
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:13:41.058913+00:00
-- url     : https://prove2.me/theorems/f0e8ca03-ffdc-4aef-a828-1837edc8421f
-- title:
--   `BookProof.SmHiggsVacuum.higgsV_sq_form` {lam mu2 : ℝ} (hlam : 0 < lam) (phi : E) : higgsV lam mu2 phi = (lam / 4) * (‖phi‖ ^ 2 - mu2 / lam) ^ 2 - mu2 ^ 2 / (4 * lam)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmHiggsVacuum`.
--
--   `BookProof.SmHiggsVacuum.higgsV_sq_form` {lam mu2 : ℝ} (hlam : 0 < lam) (phi : E) : higgsV lam mu2 phi = (lam / 4) * (‖phi‖ ^ 2 - mu2 / lam) ^ 2 - mu2 ^ 2 / (4 * lam)
--
--   Formalization note: Lean 4 identifier `BookProof.SmHiggsVacuum.higgsV_sq_form`.

-- Generated from ChapterSmHiggsVacuum.lean — theorem BookProof.SmHiggsVacuum.higgsV_sq_form
import Mathlib
import Definitions.Def_ChapterSmHiggsVacuum
open BookProof.SmHiggsVacuum



open Finset

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem BookProof.SmHiggsVacuum.higgsV_sq_form {lam mu2 : ℝ} (hlam : 0 < lam) (phi : E) :
    higgsV lam mu2 phi = (lam / 4) * (‖phi‖ ^ 2 - mu2 / lam) ^ 2 - mu2 ^ 2 / (4 * lam) := by sorry

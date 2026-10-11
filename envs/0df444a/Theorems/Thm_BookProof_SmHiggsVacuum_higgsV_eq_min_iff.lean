-- Prove2me | Theorems.Thm_BookProof_SmHiggsVacuum_higgsV_eq_min_iff
-- name    : BookProof.SmHiggsVacuum.higgsV_eq_min_iff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:13:19.804058+00:00
-- url     : https://prove2.me/theorems/7a362e72-a450-4884-8e6f-bb91750c13ae
-- title:
--   `BookProof.SmHiggsVacuum.higgsV_eq_min_iff` {lam mu2 : ℝ} (hlam : 0 < lam) (phi : E) : higgsV lam mu2 phi = -(mu2 ^ 2 / (4 * lam)) ↔ ‖phi‖ ^ 2 = mu2 / lam
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmHiggsVacuum`.
--
--   `BookProof.SmHiggsVacuum.higgsV_eq_min_iff` {lam mu2 : ℝ} (hlam : 0 < lam) (phi : E) : higgsV lam mu2 phi = -(mu2 ^ 2 / (4 * lam)) ↔ ‖phi‖ ^ 2 = mu2 / lam
--
--   Formalization note: Lean 4 identifier `BookProof.SmHiggsVacuum.higgsV_eq_min_iff`.

-- Generated from ChapterSmHiggsVacuum.lean — theorem BookProof.SmHiggsVacuum.higgsV_eq_min_iff
import Mathlib
import Definitions.Def_ChapterSmHiggsVacuum
open BookProof.SmHiggsVacuum



open Finset

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem BookProof.SmHiggsVacuum.higgsV_eq_min_iff {lam mu2 : ℝ} (hlam : 0 < lam) (phi : E) :
    higgsV lam mu2 phi = -(mu2 ^ 2 / (4 * lam)) ↔ ‖phi‖ ^ 2 = mu2 / lam := by sorry

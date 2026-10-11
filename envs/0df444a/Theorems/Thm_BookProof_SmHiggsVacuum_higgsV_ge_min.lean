-- Prove2me | Theorems.Thm_BookProof_SmHiggsVacuum_higgsV_ge_min
-- name    : BookProof.SmHiggsVacuum.higgsV_ge_min
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:13:05.791549+00:00
-- url     : https://prove2.me/theorems/4f2ae1a8-022d-4093-89d1-fdee16123397
-- title:
--   `BookProof.SmHiggsVacuum.higgsV_ge_min` {lam mu2 : ℝ} (hlam : 0 < lam) (phi : E) : -(mu2 ^ 2 / (4 * lam)) ≤ higgsV lam mu2 phi
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmHiggsVacuum`.
--
--   `BookProof.SmHiggsVacuum.higgsV_ge_min` {lam mu2 : ℝ} (hlam : 0 < lam) (phi : E) : -(mu2 ^ 2 / (4 * lam)) ≤ higgsV lam mu2 phi
--
--   Formalization note: Lean 4 identifier `BookProof.SmHiggsVacuum.higgsV_ge_min`.

-- Generated from ChapterSmHiggsVacuum.lean — theorem BookProof.SmHiggsVacuum.higgsV_ge_min
import Mathlib
import Definitions.Def_ChapterSmHiggsVacuum
open BookProof.SmHiggsVacuum



open Finset

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem BookProof.SmHiggsVacuum.higgsV_ge_min {lam mu2 : ℝ} (hlam : 0 < lam) (phi : E) :
    -(mu2 ^ 2 / (4 * lam)) ≤ higgsV lam mu2 phi := by sorry

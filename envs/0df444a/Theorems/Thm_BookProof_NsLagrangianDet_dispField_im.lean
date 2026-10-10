-- Prove2me | Theorems.Thm_BookProof_NsLagrangianDet_dispField_im
-- name    : BookProof.NsLagrangianDet.dispField_im
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T07:55:38.873946+00:00
-- url     : https://prove2.me/theorems/19a76a34-7c42-433b-98d1-917bf03b0ef3
-- title:
--   `BookProof.NsLagrangianDet.dispField_im` (kv : K → Fin 3 → ℝ) (y : DIdx K → ℝ) (a : Fin 3 → ℝ) (i : Fin 3) : (dispField kv y a i).im = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsLagrangianDetConvolution`.
--
--   `BookProof.NsLagrangianDet.dispField_im` (kv : K → Fin 3 → ℝ) (y : DIdx K → ℝ) (a : Fin 3 → ℝ) (i : Fin 3) : (dispField kv y a i).im = 0
--
--   Formalization note: Lean 4 identifier `BookProof.NsLagrangianDet.dispField_im`.

-- Generated from ChapterNsLagrangianDetConvolution.lean — theorem BookProof.NsLagrangianDet.dispField_im
import Mathlib
import Definitions.Def_ChapterNsLagrangianDetConvolution
open BookProof.NsLagrangianDet



open MvPolynomial Matrix

noncomputable section

variable {K : Type*} [Fintype K]

theorem BookProof.NsLagrangianDet.dispField_im (kv : K → Fin 3 → ℝ) (y : DIdx K → ℝ) (a : Fin 3 → ℝ) (i : Fin 3) :
    (dispField kv y a i).im = 0 := by sorry

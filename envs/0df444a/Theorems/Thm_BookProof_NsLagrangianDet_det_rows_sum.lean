-- Prove2me | Theorems.Thm_BookProof_NsLagrangianDet_det_rows_sum
-- name    : BookProof.NsLagrangianDet.det_rows_sum
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T07:55:25.016994+00:00
-- url     : https://prove2.me/theorems/c64e8233-a415-45d7-9d28-3486ea5388e1
-- title:
--   `BookProof.NsLagrangianDet.det_rows_sum` {n ι R : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [CommRing R] (v : n → ι → n → R) : (Matrix.of fun r c => ∑ o, v r o c).det = ∑ τ :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsLagrangianDetConvolution`.
--
--   `BookProof.NsLagrangianDet.det_rows_sum` {n ι R : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [CommRing R] (v : n → ι → n → R) : (Matrix.of fun r c => ∑ o, v r o c).det = ∑ τ : n → ι, (Matrix.of fun r c => v r (τ r) c).det
--
--   Formalization note: Lean 4 identifier `BookProof.NsLagrangianDet.det_rows_sum`.

-- Generated from ChapterNsLagrangianDetConvolution.lean — theorem BookProof.NsLagrangianDet.det_rows_sum
import Mathlib
import Definitions.Def_ChapterNsLagrangianDetConvolution
open BookProof.NsLagrangianDet



open MvPolynomial Matrix

noncomputable section

variable {K : Type*} [Fintype K]

theorem BookProof.NsLagrangianDet.det_rows_sum {n ι R : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [CommRing R]
    (v : n → ι → n → R) :
    (Matrix.of fun r c => ∑ o, v r o c).det
      = ∑ τ : n → ι, (Matrix.of fun r c => v r (τ r) c).det := by sorry

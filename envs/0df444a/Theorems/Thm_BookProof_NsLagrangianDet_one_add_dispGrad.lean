-- Prove2me | Theorems.Thm_BookProof_NsLagrangianDet_one_add_dispGrad
-- name    : BookProof.NsLagrangianDet.one_add_dispGrad
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T07:55:15.874211+00:00
-- url     : https://prove2.me/theorems/898d4d67-80cc-4003-b3e1-26323291eb1c
-- title:
--   `BookProof.NsLagrangianDet.one_add_dispGrad` (kv : K → Fin 3 → ℝ) (y : DIdx K → ℝ) (a : Fin 3 → ℝ) : 1 + dispGrad kv y a = Matrix.of fun r c => ∑ o : Option (SMode K), ev y (rowCoe
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsLagrangianDetConvolution`.
--
--   `BookProof.NsLagrangianDet.one_add_dispGrad` (kv : K → Fin 3 → ℝ) (y : DIdx K → ℝ) (a : Fin 3 → ℝ) : 1 + dispGrad kv y a = Matrix.of fun r c => ∑ o : Option (SMode K), ev y (rowCoef kv o r c) * ophase kv a o
--
--   Formalization note: Lean 4 identifier `BookProof.NsLagrangianDet.one_add_dispGrad`.

-- Generated from ChapterNsLagrangianDetConvolution.lean — theorem BookProof.NsLagrangianDet.one_add_dispGrad
import Mathlib
import Definitions.Def_ChapterNsLagrangianDetConvolution
open BookProof.NsLagrangianDet



open MvPolynomial Matrix

noncomputable section

variable {K : Type*} [Fintype K]

theorem BookProof.NsLagrangianDet.one_add_dispGrad (kv : K → Fin 3 → ℝ) (y : DIdx K → ℝ) (a : Fin 3 → ℝ) :
    1 + dispGrad kv y a
      = Matrix.of fun r c => ∑ o : Option (SMode K), ev y (rowCoef kv o r c) * ophase kv a o := by sorry

-- Prove2me | Theorems.Thm_BookProof_NsLagrangianDet_det_eq_one_of_volPot_eq_zero
-- name    : BookProof.NsLagrangianDet.det_eq_one_of_volPot_eq_zero
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T07:56:08.825046+00:00
-- url     : https://prove2.me/theorems/a8a79005-6614-4ef4-9630-2427e2df61d6
-- title:
--   `BookProof.NsLagrangianDet.det_eq_one_of_volPot_eq_zero` {kappa : ℝ} (hk : 0 < kappa) (kv : K → Fin 3 → ℝ) (y : DIdx K → ℝ) (h : ev y (volPot kappa kv) = 0) (a : Fin 3 → ℝ) : (1 +
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsLagrangianDetConvolution`.
--
--   `BookProof.NsLagrangianDet.det_eq_one_of_volPot_eq_zero` {kappa : ℝ} (hk : 0 < kappa) (kv : K → Fin 3 → ℝ) (y : DIdx K → ℝ) (h : ev y (volPot kappa kv) = 0) (a : Fin 3 → ℝ) : (1 + dispGrad kv y a).det = 1
--
--   Formalization note: Lean 4 identifier `BookProof.NsLagrangianDet.det_eq_one_of_volPot_eq_zero`.

-- Generated from ChapterNsLagrangianDetConvolution.lean — theorem BookProof.NsLagrangianDet.det_eq_one_of_volPot_eq_zero
import Mathlib
import Definitions.Def_ChapterNsLagrangianDetConvolution
open BookProof.NsLagrangianDet



open MvPolynomial Matrix

noncomputable section

variable {K : Type*} [Fintype K]

theorem BookProof.NsLagrangianDet.det_eq_one_of_volPot_eq_zero {kappa : ℝ} (hk : 0 < kappa) (kv : K → Fin 3 → ℝ)
    (y : DIdx K → ℝ) (h : ev y (volPot kappa kv) = 0) (a : Fin 3 → ℝ) :
    (1 + dispGrad kv y a).det = 1 := by sorry

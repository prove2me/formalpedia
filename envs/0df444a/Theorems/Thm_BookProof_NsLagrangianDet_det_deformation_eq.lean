-- Prove2me | Theorems.Thm_BookProof_NsLagrangianDet_det_deformation_eq
-- name    : BookProof.NsLagrangianDet.det_deformation_eq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T07:55:25.498836+00:00
-- url     : https://prove2.me/theorems/76c9eb6f-1d10-4e5c-aedb-38b05a3b40a7
-- title:
--   `BookProof.NsLagrangianDet.det_deformation_eq` (kv : K → Fin 3 → ℝ) (y : DIdx K → ℝ) (a : Fin 3 → ℝ) : (1 + dispGrad kv y a).det = ∑ q ∈ waveSet kv, ev y (detCoef kv q) * phase q a
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsLagrangianDetConvolution`.
--
--   `BookProof.NsLagrangianDet.det_deformation_eq` (kv : K → Fin 3 → ℝ) (y : DIdx K → ℝ) (a : Fin 3 → ℝ) : (1 + dispGrad kv y a).det = ∑ q ∈ waveSet kv, ev y (detCoef kv q) * phase q a
--
--   Formalization note: Lean 4 identifier `BookProof.NsLagrangianDet.det_deformation_eq`.

-- Generated from ChapterNsLagrangianDetConvolution.lean — theorem BookProof.NsLagrangianDet.det_deformation_eq
import Mathlib
import Definitions.Def_ChapterNsLagrangianDetConvolution
open BookProof.NsLagrangianDet



open MvPolynomial Matrix

noncomputable section

variable {K : Type*} [Fintype K]

theorem BookProof.NsLagrangianDet.det_deformation_eq (kv : K → Fin 3 → ℝ) (y : DIdx K → ℝ) (a : Fin 3 → ℝ) :
    (1 + dispGrad kv y a).det = ∑ q ∈ waveSet kv, ev y (detCoef kv q) * phase q a := by sorry

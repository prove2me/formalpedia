-- Prove2me | Theorems.Thm_BookProof_NsLagrangianDet_volume_residual_eq
-- name    : BookProof.NsLagrangianDet.volume_residual_eq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T07:55:42.778988+00:00
-- url     : https://prove2.me/theorems/352b06ee-972a-4f27-a4de-aad028b75583
-- title:
--   `BookProof.NsLagrangianDet.volume_residual_eq` (kv : K → Fin 3 → ℝ) (y : DIdx K → ℝ) (a : Fin 3 → ℝ) : (1 + dispGrad kv y a).det - 1 = ∑ q ∈ waveSet kv, ev y (volCoef kv q) * phase
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsLagrangianDetConvolution`.
--
--   `BookProof.NsLagrangianDet.volume_residual_eq` (kv : K → Fin 3 → ℝ) (y : DIdx K → ℝ) (a : Fin 3 → ℝ) : (1 + dispGrad kv y a).det - 1 = ∑ q ∈ waveSet kv, ev y (volCoef kv q) * phase q a
--
--   Formalization note: Lean 4 identifier `BookProof.NsLagrangianDet.volume_residual_eq`.

-- Generated from ChapterNsLagrangianDetConvolution.lean — theorem BookProof.NsLagrangianDet.volume_residual_eq
import Mathlib
import Definitions.Def_ChapterNsLagrangianDetConvolution
open BookProof.NsLagrangianDet



open MvPolynomial Matrix

noncomputable section

variable {K : Type*} [Fintype K]

theorem BookProof.NsLagrangianDet.volume_residual_eq (kv : K → Fin 3 → ℝ) (y : DIdx K → ℝ) (a : Fin 3 → ℝ) :
    (1 + dispGrad kv y a).det - 1 = ∑ q ∈ waveSet kv, ev y (volCoef kv q) * phase q a := by sorry

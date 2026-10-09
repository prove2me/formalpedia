-- Prove2me | Theorems.Thm_BookProof_QuantumGravity3DGauge_signedOp_apply
-- name    : BookProof.QuantumGravity3DGauge.signedOp_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T09:33:21.010954+00:00
-- url     : https://prove2.me/theorems/843d3e4d-1bcb-477a-8377-80076d34d75b
-- title:
--   The Lean 4 theorem `signedOp_apply` in the `ChapterQuantumGravity3DGauge` chapter of the timepiece formalization
-- statement:
--   Formal statement of `BookProof.QuantumGravity3DGauge.signedOp_apply` from the timepiece Lean 4 formalization.
-- source:
--   https://github.com/leonardopedro/timepiece

-- Generated from ChapterQuantumGravity3DGauge.lean — theorem BookProof.QuantumGravity3DGauge.signedOp_apply
import Mathlib
import Definitions.Def_ChapterQuantumGravity3DGauge
open BookProof.QuantumGravity3DGauge



open MeasureTheory Complex MvPolynomial Filter Topology
open BookProof.HermiteProductCore BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.HermiteGalerkin
open BookProof.HashimotoShiftInvert BookProof.QuantumGravityDensitized

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

theorem BookProof.QuantumGravity3DGauge.signedOp_apply {n m : ℕ} (kappa : Fin n → ℝ) (pi : Fin n → D →ₗ[ℂ] D)
    (Bf : Fin m → D →ₗ[ℂ] D) (x : D) :
    signedOp kappa pi Bf x
      = ((1 / 2 : ℝ) : ℂ)
        • ((∑ i, ((kappa i : ℝ) : ℂ) • ((pi i (pi i x) : D) : F))
            + ∑ a, ((Bf a (Bf a x) : D) : F)) := by sorry

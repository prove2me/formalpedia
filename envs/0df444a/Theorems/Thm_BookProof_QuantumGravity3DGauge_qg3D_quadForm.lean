-- Prove2me | Theorems.Thm_BookProof_QuantumGravity3DGauge_qg3D_quadForm
-- name    : BookProof.QuantumGravity3DGauge.qg3D_quadForm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T19:35:59.103772+00:00
-- url     : https://prove2.me/theorems/0d0ba3d7-0da0-402e-87a2-20dd254e5f28
-- title:
--   The Lean 4 theorem `qg3D_quadForm` in the `ChapterQuantumGravity3DGauge` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `qg3D_quadForm` in the `ChapterQuantumGravity3DGauge` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQuantumGravity3DGauge.lean

-- Generated from ChapterQuantumGravity3DGauge.lean — theorem BookProof.QuantumGravity3DGauge.qg3D_quadForm
import Mathlib
import Definitions.Def_ChapterQuantumGravity3DGauge
open BookProof.QuantumGravity3DGauge



open MeasureTheory Complex MvPolynomial Filter Topology
open BookProof.HermiteProductCore BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.HermiteGalerkin
open BookProof.HashimotoShiftInvert BookProof.QuantumGravityDensitized

noncomputable section

variable {D : Submodule ℂ (L2d 84)}

theorem BookProof.QuantumGravity3DGauge.qg3D_quadForm (Φ : CoreRep 84 D) (x : D) :
    quadForm (qg3DHamiltonian Φ) x
      = 1 / 2 * (∑ j, qgKappa j * ‖((qgMom Φ j x : D) : L2d 84)‖ ^ 2)
        + 1 / 2 * ∑ m, ‖((torsionOps Φ m x : D) : L2d 84)‖ ^ 2 := by sorry

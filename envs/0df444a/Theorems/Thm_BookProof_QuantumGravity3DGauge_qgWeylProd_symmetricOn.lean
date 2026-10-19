-- Prove2me | Theorems.Thm_BookProof_QuantumGravity3DGauge_qgWeylProd_symmetricOn
-- name    : BookProof.QuantumGravity3DGauge.qgWeylProd_symmetricOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T19:35:51.101976+00:00
-- url     : https://prove2.me/theorems/b034e47a-79e0-4bde-80e2-6c1a80cedbd8
-- title:
--   The Lean 4 theorem `qgWeylProd_symmetricOn` in the `ChapterQuantumGravity3DGauge` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `qgWeylProd_symmetricOn` in the `ChapterQuantumGravity3DGauge` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQuantumGravity3DGauge.lean

-- Generated from ChapterQuantumGravity3DGauge.lean — theorem BookProof.QuantumGravity3DGauge.qgWeylProd_symmetricOn
import Mathlib
import Definitions.Def_ChapterQuantumGravity3DGauge
open BookProof.QuantumGravity3DGauge



open MeasureTheory Complex MvPolynomial Filter Topology
open BookProof.HermiteProductCore BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.HermiteGalerkin
open BookProof.HashimotoShiftInvert BookProof.QuantumGravityDensitized

noncomputable section

variable {D : Submodule ℂ (L2d 84)}

theorem BookProof.QuantumGravity3DGauge.qgWeylProd_symmetricOn (Φ : CoreRep 84 D) (j k : Fin 84) :
    SymmetricOn D (D.subtype.comp (Φ.op (qgWeylProd (mulOp (X j)) (momOp k)))) := by sorry

-- Prove2me | Theorems.Thm_BookProof_QuantumGravity3DGauge_qgWeylProd_coord_mom_polySym
-- name    : BookProof.QuantumGravity3DGauge.qgWeylProd_coord_mom_polySym
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T09:34:39.859979+00:00
-- url     : https://prove2.me/theorems/dd5e61fa-3ef0-481f-b597-c3ac6c94f1b0
-- title:
--   The Lean 4 theorem `qgWeylProd_coord_mom_polySym` in the `ChapterQuantumGravity3DGauge` chapter of the timepiece formalization
-- statement:
--   Formal statement of `BookProof.QuantumGravity3DGauge.qgWeylProd_coord_mom_polySym` from the timepiece Lean 4 formalization.
-- source:
--   https://github.com/leonardopedro/timepiece

-- Generated from ChapterQuantumGravity3DGauge.lean — theorem BookProof.QuantumGravity3DGauge.qgWeylProd_coord_mom_polySym
import Mathlib
import Definitions.Def_ChapterQuantumGravity3DGauge
open BookProof.QuantumGravity3DGauge



open MeasureTheory Complex MvPolynomial Filter Topology
open BookProof.HermiteProductCore BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.HermiteGalerkin
open BookProof.HashimotoShiftInvert BookProof.QuantumGravityDensitized

noncomputable section

variable {d : ℕ}

theorem BookProof.QuantumGravity3DGauge.qgWeylProd_coord_mom_polySym (j k : Fin d) :
    PolySym (qgWeylProd (mulOp (X j)) (momOp k)) := by sorry

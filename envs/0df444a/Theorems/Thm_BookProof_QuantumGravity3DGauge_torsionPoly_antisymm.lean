-- Prove2me | Theorems.Thm_BookProof_QuantumGravity3DGauge_torsionPoly_antisymm
-- name    : BookProof.QuantumGravity3DGauge.torsionPoly_antisymm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-22T03:48:14.618303+00:00
-- url     : https://prove2.me/theorems/d680d33a-170b-4c32-93e2-bb72aaab625f
-- title:
--   The Lean 4 theorem `torsionPoly_antisymm` in the `ChapterQuantumGravity3DGauge` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `torsionPoly_antisymm` in the `ChapterQuantumGravity3DGauge` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQuantumGravity3DGauge.lean

-- Generated from ChapterQuantumGravity3DGauge.lean — theorem BookProof.QuantumGravity3DGauge.torsionPoly_antisymm
import Mathlib
import Definitions.Def_ChapterQuantumGravity3DGauge
open BookProof.QuantumGravity3DGauge



open MeasureTheory Complex MvPolynomial Filter Topology
open BookProof.HermiteProductCore BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.HermiteGalerkin
open BookProof.HashimotoShiftInvert BookProof.QuantumGravityDensitized

noncomputable section

theorem BookProof.QuantumGravity3DGauge.torsionPoly_antisymm (mu nu a : Fin 4) :
    torsionPoly mu nu a = -torsionPoly nu mu a := by sorry

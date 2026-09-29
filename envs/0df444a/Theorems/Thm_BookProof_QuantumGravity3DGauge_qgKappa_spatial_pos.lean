-- Prove2me | Theorems.Thm_BookProof_QuantumGravity3DGauge_qgKappa_spatial_pos
-- name    : BookProof.QuantumGravity3DGauge.qgKappa_spatial_pos
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-22T03:48:15.523143+00:00
-- url     : https://prove2.me/theorems/a63a0ed8-5e87-4c7a-9585-2765868a6210
-- title:
--   The Lean 4 theorem `qgKappa_spatial_pos` in the `ChapterQuantumGravity3DGauge` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `qgKappa_spatial_pos` in the `ChapterQuantumGravity3DGauge` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQuantumGravity3DGauge.lean

-- Generated from ChapterQuantumGravity3DGauge.lean — theorem BookProof.QuantumGravity3DGauge.qgKappa_spatial_pos
import Mathlib
import Definitions.Def_ChapterQuantumGravity3DGauge
open BookProof.QuantumGravity3DGauge



open MeasureTheory Complex MvPolynomial Filter Topology
open BookProof.HermiteProductCore BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.HermiteGalerkin
open BookProof.HashimotoShiftInvert BookProof.QuantumGravityDensitized

noncomputable section

theorem BookProof.QuantumGravity3DGauge.qgKappa_spatial_pos {j : Fin 84} (hj : j ≠ confIndex) : 0 < qgKappa j := by sorry

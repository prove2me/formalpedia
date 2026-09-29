-- Prove2me | Theorems.Thm_BookProof_QuantumGravity3DGauge_idxX_ne_idxE
-- name    : BookProof.QuantumGravity3DGauge.idxX_ne_idxE
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-22T03:47:21.509241+00:00
-- url     : https://prove2.me/theorems/95be8f07-3b9a-4da7-a4a3-a35049126e9b
-- title:
--   The Lean 4 theorem `idxX_ne_idxE` in the `ChapterQuantumGravity3DGauge` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `idxX_ne_idxE` in the `ChapterQuantumGravity3DGauge` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQuantumGravity3DGauge.lean

-- Generated from ChapterQuantumGravity3DGauge.lean — theorem BookProof.QuantumGravity3DGauge.idxX_ne_idxE
import Mathlib
import Definitions.Def_ChapterQuantumGravity3DGauge
open BookProof.QuantumGravity3DGauge



open MeasureTheory Complex MvPolynomial Filter Topology
open BookProof.HermiteProductCore BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.HermiteGalerkin
open BookProof.HashimotoShiftInvert BookProof.QuantumGravityDensitized

noncomputable section

theorem BookProof.QuantumGravity3DGauge.idxX_ne_idxE (mu nu a : Fin 4) : idxX mu ≠ idxE nu a := by sorry

-- Prove2me | Theorems.Thm_BookProof_QuantumGravity3DGauge_idxX_injective
-- name    : BookProof.QuantumGravity3DGauge.idxX_injective
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-22T03:47:02.585991+00:00
-- url     : https://prove2.me/theorems/cd261242-3366-4a18-b94d-88cb4ed3f9a9
-- title:
--   The Lean 4 theorem `idxX_injective` in the `ChapterQuantumGravity3DGauge` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `idxX_injective` in the `ChapterQuantumGravity3DGauge` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQuantumGravity3DGauge.lean

-- Generated from ChapterQuantumGravity3DGauge.lean — theorem BookProof.QuantumGravity3DGauge.idxX_injective
import Mathlib
import Definitions.Def_ChapterQuantumGravity3DGauge
open BookProof.QuantumGravity3DGauge



open MeasureTheory Complex MvPolynomial Filter Topology
open BookProof.HermiteProductCore BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.HermiteGalerkin
open BookProof.HashimotoShiftInvert BookProof.QuantumGravityDensitized

noncomputable section

theorem BookProof.QuantumGravity3DGauge.idxX_injective : Function.Injective idxX := by sorry

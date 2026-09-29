-- Prove2me | Theorems.Thm_BookProof_QuantumGravity3DGauge_idxDE_injective
-- name    : BookProof.QuantumGravity3DGauge.idxDE_injective
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-22T03:46:42.917549+00:00
-- url     : https://prove2.me/theorems/0dffabc9-96d8-4e97-a078-0c27e8cbcff6
-- title:
--   The Lean 4 theorem `idxDE_injective` in the `ChapterQuantumGravity3DGauge` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `idxDE_injective` in the `ChapterQuantumGravity3DGauge` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQuantumGravity3DGauge.lean

-- Generated from ChapterQuantumGravity3DGauge.lean — theorem BookProof.QuantumGravity3DGauge.idxDE_injective
import Mathlib
import Definitions.Def_ChapterQuantumGravity3DGauge
open BookProof.QuantumGravity3DGauge



open MeasureTheory Complex MvPolynomial Filter Topology
open BookProof.HermiteProductCore BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.HermiteGalerkin
open BookProof.HashimotoShiftInvert BookProof.QuantumGravityDensitized

noncomputable section

theorem BookProof.QuantumGravity3DGauge.idxDE_injective :
    Function.Injective (fun q : Fin 4 × Fin 4 × Fin 4 => idxDE q.1 q.2.1 q.2.2) := by sorry

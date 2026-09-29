-- Prove2me | Theorems.Thm_BookProof_QuantumGravity3DGauge_idxE_injective
-- name    : BookProof.QuantumGravity3DGauge.idxE_injective
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-22T03:46:56.832722+00:00
-- url     : https://prove2.me/theorems/0be30249-6150-4f4d-80a4-0aec982046bd
-- title:
--   The Lean 4 theorem `idxE_injective` in the `ChapterQuantumGravity3DGauge` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `idxE_injective` in the `ChapterQuantumGravity3DGauge` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQuantumGravity3DGauge.lean

-- Generated from ChapterQuantumGravity3DGauge.lean — theorem BookProof.QuantumGravity3DGauge.idxE_injective
import Mathlib
import Definitions.Def_ChapterQuantumGravity3DGauge
open BookProof.QuantumGravity3DGauge



open MeasureTheory Complex MvPolynomial Filter Topology
open BookProof.HermiteProductCore BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.HermiteGalerkin
open BookProof.HashimotoShiftInvert BookProof.QuantumGravityDensitized

noncomputable section

theorem BookProof.QuantumGravity3DGauge.idxE_injective : Function.Injective (fun q : Fin 4 × Fin 4 => idxE q.1 q.2) := by sorry

-- Prove2me | Theorems.Thm_BookProof_QuantumGravity3DGauge_qg3DDensity_densitized
-- name    : BookProof.QuantumGravity3DGauge.qg3DDensity_densitized
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-22T03:47:28.794557+00:00
-- url     : https://prove2.me/theorems/b497bfa9-e1e3-4cd0-b232-bd90fa1d46ca
-- title:
--   The Lean 4 theorem `qg3DDensity_densitized` in the `ChapterQuantumGravity3DGauge` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `qg3DDensity_densitized` in the `ChapterQuantumGravity3DGauge` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQuantumGravity3DGauge.lean

-- Generated from ChapterQuantumGravity3DGauge.lean — theorem BookProof.QuantumGravity3DGauge.qg3DDensity_densitized
import Mathlib
import Definitions.Def_ChapterQuantumGravity3DGauge
open BookProof.QuantumGravity3DGauge



open MeasureTheory Complex MvPolynomial Filter Topology
open BookProof.HermiteProductCore BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.HermiteGalerkin
open BookProof.HashimotoShiftInvert BookProof.QuantumGravityDensitized

noncomputable section

theorem BookProof.QuantumGravity3DGauge.qg3DDensity_densitized (e s p : ℝ) (he : 0 < e) :
    qg3DDensity e s p = 1 / 16 * (s / densY e) ^ 2 - 1 / 24 * (p / densY e) ^ 2 := by sorry

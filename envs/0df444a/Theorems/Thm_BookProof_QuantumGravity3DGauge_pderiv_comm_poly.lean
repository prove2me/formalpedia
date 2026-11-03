-- Prove2me | Theorems.Thm_BookProof_QuantumGravity3DGauge_pderiv_comm_poly
-- name    : BookProof.QuantumGravity3DGauge.pderiv_comm_poly
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-03T04:36:49.353059+00:00
-- url     : https://prove2.me/theorems/ddca4c59-0a4a-4a4e-ad86-cb0e602778fa
-- title:
--   The Lean 4 theorem `pderiv_comm_poly` in the `ChapterQuantumGravity3DGauge` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `pderiv_comm_poly` in the `ChapterQuantumGravity3DGauge` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQuantumGravity3DGauge.lean

-- Generated from ChapterQuantumGravity3DGauge.lean — theorem BookProof.QuantumGravity3DGauge.pderiv_comm_poly
import Mathlib
import Definitions.Def_ChapterQuantumGravity3DGauge
open BookProof.QuantumGravity3DGauge



open MeasureTheory Complex MvPolynomial Filter Topology
open BookProof.HermiteProductCore BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.HermiteGalerkin
open BookProof.HashimotoShiftInvert BookProof.QuantumGravityDensitized

noncomputable section

theorem BookProof.QuantumGravity3DGauge.pderiv_comm_poly {d : ℕ} (j k : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    pderiv j (pderiv k p) = pderiv k (pderiv j p) := by sorry

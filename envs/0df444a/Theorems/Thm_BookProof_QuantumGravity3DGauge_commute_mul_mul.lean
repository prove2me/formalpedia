-- Prove2me | Theorems.Thm_BookProof_QuantumGravity3DGauge_commute_mul_mul
-- name    : BookProof.QuantumGravity3DGauge.commute_mul_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-03T08:09:03.297545+00:00
-- url     : https://prove2.me/theorems/30c9dbb5-a31e-4ceb-b2fb-f5845fe5be4a
-- title:
--   The Lean 4 theorem `commute_mul_mul` in the `ChapterQuantumGravity3DGauge` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `commute_mul_mul` in the `ChapterQuantumGravity3DGauge` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQuantumGravity3DGauge.lean

-- Generated from ChapterQuantumGravity3DGauge.lean — theorem BookProof.QuantumGravity3DGauge.commute_mul_mul
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterQuantumGravityDensitized
import Mathlib
import Definitions.Def_ChapterQuantumGravity3DGauge
import Definitions.Def_ChapterF7
open BookProof.ChapterF7
open BookProof.QuantumGravity3DGauge

variable {d : ℕ}



open MeasureTheory Complex MvPolynomial Filter Topology
open BookProof.HermiteProductCore BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.HermiteGalerkin
open BookProof.HashimotoShiftInvert BookProof.QuantumGravityDensitized

noncomputable section

theorem BookProof.QuantumGravity3DGauge.commute_mul_mul (j k : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    momOp j (momOp k p) = momOp k (momOp j p) := by sorry

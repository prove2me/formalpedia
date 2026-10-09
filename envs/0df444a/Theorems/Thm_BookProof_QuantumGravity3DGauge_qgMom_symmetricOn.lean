-- Prove2me | Theorems.Thm_BookProof_QuantumGravity3DGauge_qgMom_symmetricOn
-- name    : BookProof.QuantumGravity3DGauge.qgMom_symmetricOn
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T22:45:14.606131+00:00
-- url     : https://prove2.me/theorems/9d93a365-72e6-4e96-b0d5-f1f6021217c7
-- title:
--   The Lean 4 theorem `qgMom_symmetricOn` in the `ChapterQuantumGravity3DGauge` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `qgMom_symmetricOn` in the `ChapterQuantumGravity3DGauge` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQuantumGravity3DGauge.lean

-- Generated from ChapterQuantumGravity3DGauge.lean — theorem BookProof.QuantumGravity3DGauge.qgMom_symmetricOn
import Mathlib
import Definitions.Def_ChapterQuantumGravity3DGauge
open BookProof.QuantumGravity3DGauge



open MeasureTheory Complex MvPolynomial Filter Topology
open BookProof.HermiteProductCore BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.HermiteGalerkin
open BookProof.HashimotoShiftInvert BookProof.QuantumGravityDensitized

noncomputable section

variable {D : Submodule ℂ (L2d 84)}

theorem BookProof.QuantumGravity3DGauge.qgMom_symmetricOn (Φ : CoreRep 84 D) (j : Fin 84) :
    SymmetricOn D (D.subtype.comp (qgMom Φ j)) := by sorry

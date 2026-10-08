-- Prove2me | Theorems.Thm_BookProof_QuantumGravity3DGauge_qg3DElliptic_eq_weylOp
-- name    : BookProof.QuantumGravity3DGauge.qg3DElliptic_eq_weylOp
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-05T18:30:45.391845+00:00
-- url     : https://prove2.me/theorems/00aca4f3-cfa8-46e0-9697-b86b5af6cde9
-- title:
--   The Lean 4 theorem `qg3DElliptic_eq_weylOp` in the `ChapterQuantumGravity3DGauge` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `qg3DElliptic_eq_weylOp` in the `ChapterQuantumGravity3DGauge` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQuantumGravity3DGauge.lean

-- Generated from ChapterQuantumGravity3DGauge.lean — theorem BookProof.QuantumGravity3DGauge.qg3DElliptic_eq_weylOp
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterQuantumGravityDensitized
import Mathlib
import Definitions.Def_ChapterQuantumGravity3DGauge
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsHermite
open BookProof.HermiteProductCore
open BookProof.YangMillsFriedrichs
open BookProof.YangMillsHermite
open BookProof.QuantumGravity3DGauge

variable {d : ℕ}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable {D : Submodule ℂ (L2d 84)}



open MeasureTheory Complex MvPolynomial Filter Topology
open BookProof.HermiteProductCore BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.HermiteGalerkin
open BookProof.HashimotoShiftInvert BookProof.QuantumGravityDensitized

noncomputable section

theorem BookProof.QuantumGravity3DGauge.qg3DElliptic_eq_weylOp (Φ : CoreRep 84 D) (j : Fin 84) :
    SymmetricOn D (D.subtype.comp
      (((Real.sqrt (qgKappaElliptic j) : ℝ) : ℂ) • qgMom Φ j)) := by sorry

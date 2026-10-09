-- Prove2me | Theorems.Thm_BookProof_QuantumGravity3DGauge_torsionOps_symmetricOn
-- name    : BookProof.QuantumGravity3DGauge.torsionOps_symmetricOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T08:25:19.594067+00:00
-- url     : https://prove2.me/theorems/78d6aafa-3572-4f90-a698-54f5218f87a7
-- title:
--   The Lean 4 theorem `torsionOps_symmetricOn` in the `ChapterQuantumGravity3DGauge` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `torsionOps_symmetricOn` in the `ChapterQuantumGravity3DGauge` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQuantumGravity3DGauge.lean

-- Generated from ChapterQuantumGravity3DGauge.lean — theorem BookProof.QuantumGravity3DGauge.torsionOps_symmetricOn
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterQuantumGravityDensitized
import Mathlib
import Definitions.Def_ChapterQuantumGravity3DGauge
import Definitions.Def_ChapterF7
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsHermite
open BookProof.ChapterF7
open BookProof.HermiteProductCore
open BookProof.YangMillsHermite
open BookProof.QuantumGravity3DGauge



open MeasureTheory Complex MvPolynomial Filter Topology
open BookProof.HermiteProductCore BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.HermiteGalerkin
open BookProof.HashimotoShiftInvert BookProof.QuantumGravityDensitized

noncomputable section

variable {d : ℕ}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable {D : Submodule ℂ (L2d 84)}

theorem BookProof.QuantumGravity3DGauge.torsionOps_symmetricOn
    (Φ : CoreRep 84 D) (m : Fin 64) :
    SymmetricOn D (D.subtype.comp (torsionOps Φ m)) := by sorry

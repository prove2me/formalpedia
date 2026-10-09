-- Prove2me | Theorems.Thm_BookProof_QuantumGravity3DGauge_signedOp_symmetricOn
-- name    : BookProof.QuantumGravity3DGauge.signedOp_symmetricOn
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T04:57:38.490678+00:00
-- url     : https://prove2.me/theorems/fe45d9aa-618a-44f4-b9d3-ca102434b4cc
-- title:
--   The Lean 4 theorem `signedOp_symmetricOn` in the `ChapterQuantumGravity3DGauge` chapter of the timepiece formalization
-- statement:
--   Formal statement of `BookProof.QuantumGravity3DGauge.signedOp_symmetricOn` from the timepiece Lean 4 formalization.
-- source:
--   https://github.com/leonardopedro/timepiece

-- Generated from ChapterQuantumGravity3DGauge.lean — theorem BookProof.QuantumGravity3DGauge.signedOp_symmetricOn
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
import Definitions.Def_ChapterFarisLavineCore
open BookProof.QuantumGravity3DGauge



open MeasureTheory Complex MvPolynomial Filter Topology
open BookProof.HermiteProductCore BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.HermiteGalerkin
open BookProof.HashimotoShiftInvert BookProof.QuantumGravityDensitized

noncomputable section

variable {d : ℕ}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

theorem BookProof.QuantumGravity3DGauge.signedOp_symmetricOn {n m : ℕ} {kappa : Fin n → ℝ} {pi : Fin n → D →ₗ[ℂ] D}
    {Bf : Fin m → D →ₗ[ℂ] D} (hpi : ∀ i, SymmetricOn D (D.subtype.comp (pi i)))
    (hB : ∀ a, SymmetricOn D (D.subtype.comp (Bf a))) :
    SymmetricOn D (signedOp kappa pi Bf) := by sorry

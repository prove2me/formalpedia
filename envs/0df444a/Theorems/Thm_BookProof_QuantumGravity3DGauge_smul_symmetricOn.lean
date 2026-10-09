-- Prove2me | Theorems.Thm_BookProof_QuantumGravity3DGauge_smul_symmetricOn
-- name    : BookProof.QuantumGravity3DGauge.smul_symmetricOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T09:34:02.595296+00:00
-- url     : https://prove2.me/theorems/a217ee38-a745-4f65-a044-7a0d1826097a
-- title:
--   The Lean 4 theorem `smul_symmetricOn` in the `ChapterQuantumGravity3DGauge` chapter of the timepiece formalization
-- statement:
--   Formal statement of `BookProof.QuantumGravity3DGauge.smul_symmetricOn` from the timepiece Lean 4 formalization.
-- source:
--   https://github.com/leonardopedro/timepiece

-- Generated from ChapterQuantumGravity3DGauge.lean — theorem BookProof.QuantumGravity3DGauge.smul_symmetricOn
import Mathlib
import Definitions.Def_ChapterQuantumGravity3DGauge
open BookProof.QuantumGravity3DGauge



open MeasureTheory Complex MvPolynomial Filter Topology
open BookProof.HermiteProductCore BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.HermiteGalerkin
open BookProof.HashimotoShiftInvert BookProof.QuantumGravityDensitized

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

theorem BookProof.QuantumGravity3DGauge.smul_symmetricOn {T : D →ₗ[ℂ] D} (r : ℝ)
    (hT : SymmetricOn D (D.subtype.comp T)) :
    SymmetricOn D (D.subtype.comp (((r : ℝ) : ℂ) • T)) := by sorry

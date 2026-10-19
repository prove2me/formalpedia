-- Prove2me | Theorems.Thm_Ehrhart_RadialPhysicalInverseSquareRootEnergy_complexPositiveInverseSquareRootAction_pairing
-- name    : Ehrhart.RadialPhysicalInverseSquareRootEnergy.complexPositiveInverseSquareRootAction_pairing
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:04.613882+00:00
-- url     : https://prove2.me/theorems/32ad5cc2-5819-4228-8cd9-b62eb53d7a38
-- title:
--   Ehrhart.RadialPhysicalInverseSquareRootEnergy.complexPositiveInverseSquareRootAction_pairing
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | EhrhartVolumeInequality | external Lean 4.33.1 validation; bundle SHA256 7150ea60aef8441515028279454832b05d0f964f3966505d147b2c1d8afe9763

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.RadialPhysicalInverseSquareRootEnergy
open Set Function Filter MeasureTheory Matrix
open RadialSchurBlock
open scoped BigOperators ENNReal ComplexConjugate ComplexOrder
  InnerProductSpace MatrixOrder Matrix.Norms.L2Operator Topology ContDiff

theorem Ehrhart.RadialPhysicalInverseSquareRootEnergy.complexPositiveInverseSquareRootAction_pairing
    {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef)
    (b : Fin n → ℂ)
    (v : EuclideanSpace ℂ (Fin n)) :
    @inner ℂ (EuclideanSpace ℂ (Fin n)) _
      (Matrix.toEuclideanLin ((CFC.sqrt A)⁻¹)
        (WithLp.toLp 2 (star b)))
      (Matrix.toEuclideanLin (CFC.sqrt A) v) =
      b ⬝ᵥ (fun i : Fin n => v i) := by sorry

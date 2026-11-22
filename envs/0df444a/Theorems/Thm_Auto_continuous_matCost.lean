-- Prove2me | Theorems.Thm_Auto_continuous_matCost
-- name    : Auto.continuous_matCost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:50:25.883567+00:00
-- url     : https://prove2.me/theorems/c45a0d8d-313d-4409-955c-bb6b796d05eb
-- title:
--   Auto: continuous mat Cost
-- statement:
--   The Auto construction uses the continuous mat Cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4684-L4701
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4684-L4701

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
open Auto
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : Type*} [TopologicalSpace X]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem Auto.continuous_matCost {Γ K : X → Matrix κ κ ℂ} (hΓ : Continuous Γ) (hK : Continuous K)
    (hpsd : ∀ x, (Γ x).PosSemidef) {η : ℝ} (hη : 0 < η) :
    Continuous fun x => (matCost (Γ x + (η : ℂ) • 1) (K x)).toReal := by sorry

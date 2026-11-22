-- Prove2me | Theorems.Thm_Auto_rowMat_cost_unitary
-- name    : Auto.rowMat_cost_unitary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:44:25.251205+00:00
-- url     : https://prove2.me/theorems/a5bfd5b0-b494-4972-a8e9-7f3f5e0bce6f
-- title:
--   Auto: row Mat cost unitary
-- statement:
--   The Auto construction uses the row Mat cost unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2831-L2841
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2831-L2841

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
open Auto
noncomputable section
attribute [local instance] Auto._p2m_local_instance_5846efa9ac_1611
attribute [local instance] Auto._p2m_local_instance_5846efa9ac_1612
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (W0 W1 W2 D0 D1 D2 : Matrix ι ι ℂ)

theorem Auto.rowMat_cost_unitary (R : Matrix ι (ι ⊕ ι) ℂ) (Uu : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ)
    (hU : Uu * Uuᴴ = 1) (Dv : Matrix ι ι ℂ) :
    matCost ((R * Uu)ᴴ * (R * Uu)) ((R * Uu)ᴴ * Dv * (R * Uu)) = matCost (Rᴴ * R) (Rᴴ * Dv * R) := by sorry

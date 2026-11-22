-- Prove2me | Theorems.Thm_Auto_sqrt_hsSq_sqrt_sub_le
-- name    : Auto.sqrt_hsSq_sqrt_sub_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:47:59.899455+00:00
-- url     : https://prove2.me/theorems/6254620a-586a-4754-bfe9-e6145a0e734b
-- title:
--   Auto: sqrt hs Sq sqrt sub le
-- statement:
--   The Auto construction uses the sqrt hs Sq sqrt sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3876-L3893
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3876-L3893

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
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem Auto.sqrt_hsSq_sqrt_sub_le {Y₁ Y₂ : Matrix n n ℂ} {η : ℝ} (hη : 0 < η)
    (h₁ : (Y₁ - (η : ℂ) • (1 : Matrix n n ℂ)).PosSemidef)
    (h₂ : (Y₂ - (η : ℂ) • (1 : Matrix n n ℂ)).PosSemidef) :
    √(hsSq (CFC.sqrt Y₁ - CFC.sqrt Y₂)) ≤ √(hsSq (Y₁ - Y₂)) / (√η + √η) := by sorry

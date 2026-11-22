-- Prove2me | Theorems.Thm_Auto_matCost_toReal_le_hsSq
-- name    : Auto.matCost_toReal_le_hsSq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:49:34.177807+00:00
-- url     : https://prove2.me/theorems/32143fe9-4bbc-4de5-8cb8-8cf9c0f270ce
-- title:
--   Auto: mat Cost to Real le hs Sq
-- statement:
--   The Auto construction uses the mat Cost to Real le hs Sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4366-L4382
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4366-L4382

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
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem Auto.matCost_toReal_le_hsSq {P : Matrix κ κ ℂ} {η : ℝ} (hη : 0 < η)
    (hP : (P - (η : ℂ) • (1 : Matrix κ κ ℂ)).PosSemidef) (K : Matrix κ κ ℂ) :
    (matCost P K).toReal ≤ (3 / 4) * hsSq K / √η := by sorry

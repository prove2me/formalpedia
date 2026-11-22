-- Prove2me | Theorems.Thm_Auto_posDef_add_smul_one
-- name    : Auto.posDef_add_smul_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:22:31.884059+00:00
-- url     : https://prove2.me/theorems/ae346a98-efbe-4a16-a86a-22e0a3071eb5
-- title:
--   Auto: pos Def add smul one
-- statement:
--   The Auto construction uses the pos Def add smul one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1322-L1324
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1322-L1324

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
variable {n : Type*} [Fintype n] [DecidableEq n]
omit [Fintype n]

theorem Auto.posDef_add_smul_one {P : Matrix n n ℂ} (hP : P.PosSemidef) {η : ℝ} (hη : 0 < η) :
    (P + (η : ℂ) • (1 : Matrix n n ℂ)).PosDef := by sorry

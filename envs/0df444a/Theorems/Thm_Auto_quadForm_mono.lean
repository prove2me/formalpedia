-- Prove2me | Theorems.Thm_Auto_quadForm_mono
-- name    : Auto.quadForm_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:30:53.743812+00:00
-- url     : https://prove2.me/theorems/cbfdedaa-1d28-4611-9911-aaff131a121e
-- title:
--   Auto: quad Form mono
-- statement:
--   The Auto construction uses the quad Form mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1563-L1570
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1563-L1570

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
omit [DecidableEq n]

theorem Auto.quadForm_mono {A B : Matrix n n ℂ} (hAB : (B - A).PosSemidef) (X : Matrix n n ℂ) :
    hsRe X (A * X) + hsRe X (X * A) ≤ hsRe X (B * X) + hsRe X (X * B) := by sorry

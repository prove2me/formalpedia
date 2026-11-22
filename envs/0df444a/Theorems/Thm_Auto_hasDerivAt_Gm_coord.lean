-- Prove2me | Theorems.Thm_Auto_hasDerivAt_Gm_coord
-- name    : Auto.hasDerivAt_Gm_coord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:50:50.213954+00:00
-- url     : https://prove2.me/theorems/3d64d980-696b-4e4b-a631-e853657b0f5d
-- title:
--   Auto: has Deriv At Gm coord
-- statement:
--   The Auto construction uses the has Deriv At Gm coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4869-L4885
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4869-L4885

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
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem Auto.hasDerivAt_Gm_coord (β : ℝ) (m : ℕ) (s : ℝ) (i : Fin 3) (p : Fin 3 → ℝ) :
    HasDerivAt (fun x => Gm β m s (Function.update p i x)) (Gm β (m + 1) s p) (p i) := by sorry

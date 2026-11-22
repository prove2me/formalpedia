-- Prove2me | Theorems.Thm_Auto_costInt_eq_complete
-- name    : Auto.costInt_eq_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:48:10.504234+00:00
-- url     : https://prove2.me/theorems/5c00dadb-57ae-4a73-a02f-cd036cc9ecc7
-- title:
--   Auto: cost Int eq complete
-- statement:
--   The Auto construction uses the cost Int eq complete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3974-L3987
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3974-L3987

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
omit [DecidableEq n]

theorem Auto.costInt_eq_complete {A K X₀ : Matrix n n ℂ} (hA : A.IsHermitian)
    (hK : A * X₀ + X₀ * A = K) (X : Matrix n n ℂ) :
    costInt A K X = hsRe K X₀ - hsRe (X - X₀) (A * (X - X₀) + (X - X₀) * A) := by sorry

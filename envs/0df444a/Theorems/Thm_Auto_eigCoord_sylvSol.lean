-- Prove2me | Theorems.Thm_Auto_eigCoord_sylvSol
-- name    : Auto.eigCoord_sylvSol
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:41:30.098817+00:00
-- url     : https://prove2.me/theorems/3634a4e4-0490-4fb3-b816-3c0ebb7c0a7c
-- title:
--   Auto: eig Coord sylv Sol
-- statement:
--   The Auto construction uses the eig Coord sylv Sol property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1462-L1489
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1462-L1489

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

theorem Auto.eigCoord_sylvSol {Y : Matrix n n ℂ} (hY : Y.PosDef) (K : Matrix n n ℂ) (i j : n) :
    eigCoord hY.1 (sylvSol (CFC.sqrt Y) K) i j = eigCoord hY.1 K i j / ((√(hY.1.eigenvalues i) +
      √(hY.1.eigenvalues j) : ℝ) : ℂ) := by sorry

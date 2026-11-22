-- Prove2me | Theorems.Thm_Auto_eigCoord_sub
-- name    : Auto.eigCoord_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:41:18.238125+00:00
-- url     : https://prove2.me/theorems/7ef650d5-573e-4b70-b932-dfb9a8568aa4
-- title:
--   Auto: eig Coord sub
-- statement:
--   The Auto construction uses the eig Coord sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1025-L1027
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1025-L1027

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
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
omit [Fintype m] [DecidableEq m]

theorem Auto.eigCoord_sub {P : Matrix n n ℂ} (hP : P.IsHermitian) (K L : Matrix n n ℂ) :
    eigCoord hP (K - L) = eigCoord hP K - eigCoord hP L := by sorry

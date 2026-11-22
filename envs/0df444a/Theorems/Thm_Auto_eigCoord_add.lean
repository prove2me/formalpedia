-- Prove2me | Theorems.Thm_Auto_eigCoord_add
-- name    : Auto.eigCoord_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:41:13.416292+00:00
-- url     : https://prove2.me/theorems/3ddb4d91-4c83-428b-80f3-7e37ede875bd
-- title:
--   Auto: eig Coord add
-- statement:
--   The Auto construction uses the eig Coord add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1020-L1022
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1020-L1022

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

theorem Auto.eigCoord_add {P : Matrix n n ℂ} (hP : P.IsHermitian) (K L : Matrix n n ℂ) :
    eigCoord hP (K + L) = eigCoord hP K + eigCoord hP L := by sorry

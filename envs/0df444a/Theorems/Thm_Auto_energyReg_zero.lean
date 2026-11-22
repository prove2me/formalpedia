-- Prove2me | Theorems.Thm_Auto_energyReg_zero
-- name    : Auto.energyReg_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:40:24.618276+00:00
-- url     : https://prove2.me/theorems/9ea364af-237d-4f81-8020-98953be2bc69
-- title:
--   Auto: energy Reg zero
-- statement:
--   The Auto construction uses the energy Reg zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L754-L756
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L754-L756

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

theorem Auto.energyReg_zero (P : Matrix n n ℂ) :
    energyReg 0 P = energy P := by sorry

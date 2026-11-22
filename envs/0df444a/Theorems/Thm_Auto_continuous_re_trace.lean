-- Prove2me | Theorems.Thm_Auto_continuous_re_trace
-- name    : Auto.continuous_re_trace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:25:27.080233+00:00
-- url     : https://prove2.me/theorems/a8319867-2d37-4d7c-947a-16e862bb5c60
-- title:
--   Auto: continuous re trace
-- statement:
--   The Auto construction uses the continuous re trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4587-L4589
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4587-L4589

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
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : Type*} [TopologicalSpace X]
omit [Fintype ι] [DecidableEq ι]

theorem Auto.continuous_re_trace {κ : Type*} [Fintype κ] {M : X → Matrix κ κ ℂ} (hM : Continuous M) :
    Continuous fun x => (M x).trace.re := by sorry

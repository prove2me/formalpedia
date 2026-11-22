-- Prove2me | Theorems.Thm_Auto_trace_conj_unitary
-- name    : Auto.trace_conj_unitary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:26:22.958809+00:00
-- url     : https://prove2.me/theorems/9bdc46bd-ddee-474c-b20d-bb8c2e3ab9a9
-- title:
--   Auto: trace conj unitary
-- statement:
--   The Auto construction uses the trace conj unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L711-L713
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L711-L713

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
omit [DecidableEq m]

theorem Auto.trace_conj_unitary (U : Matrix.unitaryGroup n ℂ) (D : Matrix n n ℂ) :
    ((U : Matrix n n ℂ) * D * star (U : Matrix n n ℂ)).trace = D.trace := by sorry

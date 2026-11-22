-- Prove2me | Theorems.Thm_Auto_cyc_backward_conj
-- name    : Auto.cyc_backward_conj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:43:43.528023+00:00
-- url     : https://prove2.me/theorems/8d447383-d4ef-49fa-9e5b-839f62c3dc58
-- title:
--   Auto: cyc backward conj
-- statement:
--   The Auto construction uses the cyc backward conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2544-L2550
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2544-L2550

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
attribute [local instance] Auto._p2m_local_instance_5846efa9ac_1611
attribute [local instance] Auto._p2m_local_instance_5846efa9ac_1612
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (W0 W1 W2 D0 D1 D2 : Matrix ι ι ℂ)
omit [DecidableEq ι]

theorem Auto.cyc_backward_conj (hD0 : D0.IsHermitian) (hD1 : D1.IsHermitian) (hD2 : D2.IsHermitian) :
    (D0 * W2ᴴ * D2 * W1ᴴ * D1 * W0ᴴ).trace = star ((D0 * W0 * D1 * W1 * D2 * W2).trace) := by sorry

-- Prove2me | Theorems.Thm_Auto_trace_cube_eigen
-- name    : Auto.trace_cube_eigen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:44:06.293475+00:00
-- url     : https://prove2.me/theorems/e65f38f4-736d-4a21-8d63-6b301cd22329
-- title:
--   Auto: trace cube eigen
-- statement:
--   The Auto construction uses the trace cube eigen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2588-L2611
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2588-L2611

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

theorem Auto.trace_cube_eigen {κ : Type*} [Fintype κ] [DecidableEq κ] (U : Matrix.unitaryGroup κ ℂ)
    (m : κ → ℝ) (Dt : Matrix κ κ ℂ) :
    (((U : Matrix κ κ ℂ) * Dt * star (U : Matrix κ κ ℂ) * ((U : Matrix κ κ ℂ) * diagonal (fun i
      => (m i : ℂ)) * star (U : Matrix κ κ ℂ))) ^ 3).trace = ∑ i, ∑ j, ∑ k, ((m i * m j * m k : ℝ)
      : ℂ) * Dt i j * Dt j k * Dt k i := by sorry

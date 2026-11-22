-- Prove2me | Theorems.Thm_Auto_cycMb_isHermitian
-- name    : Auto.cycMb_isHermitian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:43:47.278674+00:00
-- url     : https://prove2.me/theorems/bb04857e-f87f-4dab-93d9-a1568f174cff
-- title:
--   Auto: cyc Mb is Hermitian
-- statement:
--   The Auto construction uses the cyc Mb is Hermitian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2553-L2555
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2553-L2555

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
omit [DecidableEq ι] [Fintype ι]

theorem Auto.cycMb_isHermitian : (blk3 (cycMb W0 W1 W2)).IsHermitian := by sorry

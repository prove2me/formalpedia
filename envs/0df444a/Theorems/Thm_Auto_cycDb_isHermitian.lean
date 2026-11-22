-- Prove2me | Theorems.Thm_Auto_cycDb_isHermitian
-- name    : Auto.cycDb_isHermitian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:43:51.998653+00:00
-- url     : https://prove2.me/theorems/9e808069-36b0-4bd9-8422-ce2ae10bbf0c
-- title:
--   Auto: cyc Db is Hermitian
-- statement:
--   The Auto construction uses the cyc Db is Hermitian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2558-L2561
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2558-L2561

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

theorem Auto.cycDb_isHermitian (hD0 : D0.IsHermitian) (hD1 : D1.IsHermitian) (hD2 : D2.IsHermitian) :
    (blk3 (cycDb D0 D1 D2)).IsHermitian := by sorry

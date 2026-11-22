-- Prove2me | Theorems.Thm_Auto_norm_diag_le
-- name    : Auto.norm_diag_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:42:54.087354+00:00
-- url     : https://prove2.me/theorems/cb916a06-a173-4cbd-91d0-30cf4a31c5bf
-- title:
--   Auto: norm diag le
-- statement:
--   The Auto construction uses the norm diag le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2169-L2176
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2169-L2176

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
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem Auto.norm_diag_le {D : Matrix κ κ ℂ} (hD : D.IsHermitian) {d : ℝ} (hd : 0 ≤ d)
    (hDd : ((d ^ 2 : ℝ) • (1 : Matrix κ κ ℂ) - D * D).PosSemidef) (i : κ) :
    ‖D i i‖ ≤ d := by sorry

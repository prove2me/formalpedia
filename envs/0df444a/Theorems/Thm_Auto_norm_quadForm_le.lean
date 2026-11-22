-- Prove2me | Theorems.Thm_Auto_norm_quadForm_le
-- name    : Auto.norm_quadForm_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:42:53.303837+00:00
-- url     : https://prove2.me/theorems/2bd81340-17cd-4ad6-92e1-4ceb4bfaa51e
-- title:
--   Auto: norm quad Form le
-- statement:
--   The Auto construction uses the norm quad Form le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2178-L2218
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2178-L2218

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

theorem Auto.norm_quadForm_le {D : Matrix κ κ ℂ} (hD : D.IsHermitian) {d : ℝ} (hd : 0 ≤ d)
    (hDd : ((d ^ 2 : ℝ) • (1 : Matrix κ κ ℂ) - D * D).PosSemidef) (v : κ → ℂ) :
    ‖∑ j, ∑ k, star (v j) * D j k * v k‖ ≤ d * ∑ j, ‖v j‖ ^ 2 := by sorry

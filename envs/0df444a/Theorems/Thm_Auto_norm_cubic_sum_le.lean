-- Prove2me | Theorems.Thm_Auto_norm_cubic_sum_le
-- name    : Auto.norm_cubic_sum_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:43:01.914802+00:00
-- url     : https://prove2.me/theorems/b3cffeb1-b694-4297-9e1f-74c978acc2e5
-- title:
--   Auto: norm cubic sum le
-- statement:
--   The Auto construction uses the norm cubic sum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2220-L2395
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2220-L2395

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

theorem Auto.norm_cubic_sum_le (m : κ → ℝ) {D : Matrix κ κ ℂ} (hD : D.IsHermitian) {d : ℝ}
    (hd : 0 ≤ d) (hDd : ((d ^ 2 : ℝ) • (1 : Matrix κ κ ℂ) - D * D).PosSemidef) :
    ‖∑ i, ∑ j, ∑ k, ((m i * m j * m k : ℝ) : ℂ) * D i j * D j k * D k i‖ ≤ 5 * d * ∑ i, ∑ j, |m
      i| ^ 2 * |m j| ^ 2 * ‖D i j‖ ^ 2 / (|m i| + |m j|) := by sorry

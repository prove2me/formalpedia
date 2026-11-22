-- Prove2me | Theorems.Thm_Auto_phi_sq_mul_exp_le
-- name    : Auto.phi_sq_mul_exp_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:36:36.372635+00:00
-- url     : https://prove2.me/theorems/43172e0c-beab-4189-bf35-16f2b7438710
-- title:
--   Auto: phi sq mul exp le
-- statement:
--   The Auto construction uses the phi sq mul exp le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4783-L4816
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4783-L4816

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

theorem Auto.phi_sq_mul_exp_le {σb τb : ℝ} (hσ : 0 < σb) (hτ : 0 < τb) (v : Fin 3) (p : Fin 3 → ℝ) :
    HeatData.phi σb v p ^ 2 * Real.exp (-(p 0 + p 1 + p 2) ^ 2 / (4 * τb)) ≤ 4 * gdom (min (1 /
      (8 * σb)) (1 / (4 * τb)) / 4) p := by sorry

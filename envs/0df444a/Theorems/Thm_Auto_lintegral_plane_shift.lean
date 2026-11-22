-- Prove2me | Theorems.Thm_Auto_lintegral_plane_shift
-- name    : Auto.lintegral_plane_shift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:53:45.065305+00:00
-- url     : https://prove2.me/theorems/fce8a1e3-3309-4218-a803-79ef76116ecf
-- title:
--   Auto: lintegral plane shift
-- statement:
--   The Auto construction uses the lintegral plane shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6669-L6699
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6669-L6699

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
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
open Auto
noncomputable section

theorem Auto.lintegral_plane_shift (v : Fin 3) {F : (Fin 3 → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ q : Fin 2 → ℝ, ∫⁻ d, F (Function.update (planePt q) v (planePt q v + d)) = ∫⁻ p, F p := by sorry

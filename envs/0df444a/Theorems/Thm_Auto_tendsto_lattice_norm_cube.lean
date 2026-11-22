-- Prove2me | Theorems.Thm_Auto_tendsto_lattice_norm_cube
-- name    : Auto.tendsto_lattice_norm_cube
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:55:22.393656+00:00
-- url     : https://prove2.me/theorems/60948f60-b648-4163-b4c9-8d6e584c80a6
-- title:
--   Auto: tendsto lattice norm cube
-- statement:
--   The Auto construction uses the tendsto lattice norm cube property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7551-L7572
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7551-L7572

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
public section
open scoped ENNReal NNReal
open MeasureTheory Filter Topology Real
public section
open Auto
open MeasureTheory Filter Topology Matrix Real
open scoped ENNReal NNReal MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section

theorem Auto.tendsto_lattice_norm_cube {Φ : ℝ × ℝ → ℂ} (hc : Continuous Φ) (hs : HasCompactSupport Φ) :
    Tendsto (fun N : ℕ => ((N : ℝ)⁻¹) ^ 2 * ∑' z : Fin 2 → ℤ, ‖Φ ((z 0 : ℝ) / N, (z 1 : ℝ) / N)‖
      ^ 3) atTop (𝓝 (∫ p, ‖Φ p‖ ^ 3)) := by sorry

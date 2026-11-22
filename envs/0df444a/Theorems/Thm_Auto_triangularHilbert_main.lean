-- Prove2me | Theorems.Thm_Auto_triangularHilbert_main
-- name    : Auto.triangularHilbert_main
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T18:58:41.658989+00:00
-- url     : https://prove2.me/theorems/0200e134-a86d-4fb7-aa7f-7643edd86798
-- title:
--   Auto: triangular Hilbert main
-- statement:
--   Source Theorem 1: existence and the uniform L3 bound for the symmetric principal value.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8651-L8661
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8651-L8661

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

theorem Auto.triangularHilbert_main :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F₀ F₁ F₂ : SchwartzMap (ℝ × ℝ) ℂ, ∃ L : ℂ,
      Tendsto (fun ε : ℝ => ∫ xyz : (ℝ × ℝ) × ℝ,
        let ((x, y), z) := xyz
        if ε < |x + y + z| then
          F₀ (x, y) * F₁ (y, z) * F₂ (z, x) / ↑(x + y + z) else 0)
        (𝓝[>] (0 : ℝ)) (𝓝 L) ∧
      ‖L‖ ≤ C * (eLpNorm F₀ 3).toReal * (eLpNorm F₁ 3).toReal * (eLpNorm F₂ 3).toReal := by sorry

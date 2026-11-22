-- Prove2me | Theorems.Thm_Auto_triangularHilbert_principal_value
-- name    : Auto.triangularHilbert_principal_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:29:22.066039+00:00
-- url     : https://prove2.me/theorems/f9c4f822-5034-477b-a25e-496f129d00e8
-- title:
--   Auto: triangular Hilbert principal value
-- statement:
--   Source Theorem 1: the displayed principal value exists for every Schwartz triple.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8374-L8378
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8374-L8378

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

theorem Auto.triangularHilbert_principal_value (F₀ F₁ F₂ : SchwartzMap (ℝ × ℝ) ℂ) :
    Tendsto (triangularHilbertTruncation F₀ F₁ F₂) (𝓝[>] (0 : ℝ)) (𝓝 (triangularHilbert F₀ F₁
      F₂)) := by sorry

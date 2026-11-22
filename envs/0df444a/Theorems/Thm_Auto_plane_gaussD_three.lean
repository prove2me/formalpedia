-- Prove2me | Theorems.Thm_Auto_plane_gaussD_three
-- name    : Auto.plane_gaussD_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:53:11.226212+00:00
-- url     : https://prove2.me/theorems/bcda7c39-309d-40bf-99a2-0d6bbdcce3d3
-- title:
--   Auto: plane gauss D three
-- statement:
--   The Auto construction uses the plane gauss D three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6293-L6346
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6293-L6346

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
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem Auto.plane_gaussD_three (d₀ d₁ d₂ : ℕ) {σ : ℝ} (hσ : 0 < σ) (c₀ c₁ c₂ : ℝ) :
    Integrable (fun q : Fin 2 → ℝ => ((gaussianD d₀ σ (c₀ - q 0) * gaussianD d₁ σ (c₁ - q 1) *
      gaussianD d₂ σ (c₂ + q 0 + q 1) : ℝ) : ℂ)) ∧ ∫ q : Fin 2 → ℝ, ((gaussianD d₀ σ (c₀ - q 0) *
      gaussianD d₁ σ (c₁ - q 1) * gaussianD d₂ σ (c₂ + q 0 + q 1) : ℝ) : ℂ) = (gaussianD (d₂ + d₁
      + d₀) (σ + σ + σ) (c₀ + c₁ + c₂) : ℂ) := by sorry

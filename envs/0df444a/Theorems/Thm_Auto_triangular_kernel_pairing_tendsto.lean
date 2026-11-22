-- Prove2me | Theorems.Thm_Auto_triangular_kernel_pairing_tendsto
-- name    : Auto.triangular_kernel_pairing_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:56:41.194597+00:00
-- url     : https://prove2.me/theorems/4701d260-a898-4e88-a5b3-978181dfdd92
-- title:
--   Auto: triangular kernel pairing tendsto
-- statement:
--   Source `dist`: dominated convergence for integrable cancelled kernel pairings.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7919-L7949
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7919-L7949

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

theorem Auto.triangular_kernel_pairing_tendsto {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {g : X → ℂ} {r : X → ℝ} (hg : Integrable g μ) (hr : Measurable r) (hz : ∀ᵐ x ∂μ, r x ≠ 0) :
    Tendsto (fun n : ℕ => ∫ x, g x * ((r x * Kern 3 ((n : ℝ) + 1)⁻¹ ((n : ℝ) + 1) (r x) : ℝ) :
      ℂ) ∂μ) atTop (𝓝 ((triangularKernelCoefficient : ℂ) * ∫ x, g x ∂μ)) := by sorry

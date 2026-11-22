-- Prove2me | Theorems.Thm_Auto_sourceGaussian_lattice_bound
-- name    : Auto.sourceGaussian_lattice_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T18:55:05.143816+00:00
-- url     : https://prove2.me/theorems/092f0419-bb93-4b93-9832-7146ecd05d59
-- title:
--   Auto: source Gaussian lattice bound
-- statement:
--   The Auto construction uses the source Gaussian lattice bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7453-L7537
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7453-L7537

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

theorem Auto.sourceGaussian_lattice_bound (F : Fin 3 → ℝ × ℝ → ℂ) {ρ : ℝ}
    (_hρ : 0 ≤ ρ) (hF : ∀ v p, ρ < ‖p‖ → F v p = 0)
    {N : ℕ} (hN : 0 < N) {a b : ℝ}
    (ha : ((N : ℝ)⁻¹) ^ 2 ≤ a) (hab : a ≤ b) :
    ‖((N : ℝ)⁻¹) ^ 3 • ∑' z : Fin 3 → ℤ,
        sourceGaussianIntegrand F a b (fun i => (z i : ℝ) / N)‖ ≤
      3 * heatBoundConstant *
        ∏ v, (((N : ℝ)⁻¹) ^ 2 *
          ∑' z : Fin 2 → ℤ, ‖F v ((z 0 : ℝ) / N, (z 1 : ℝ) / N)‖ ^ 3) ^
            (1 / 3 : ℝ) := by sorry

-- Prove2me | solution 1 for coordFunOfDet_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:24:35.182033+00:00
-- url     : https://prove2.me/submissions/23230c12-d59d-4033-939c-bfd1bf4d2f32

module
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Instances.Matrix
public import Definitions.Def_BasicResults_Auerbach

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Module FiniteDimensional Metric
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
theorem _root_.solution {n : ℕ} (b₀ : Basis (Fin n) ℝ V)
    (e : Fin n → V) (h_det : b₀.det e ≠ 0) (i : Fin n) (v : V) :
    coordFunOfDet b₀ e h_det i v = b₀.det (Function.update e i v) / b₀.det e := by
  simp [coordFunOfDet, div_eq_inv_mul]

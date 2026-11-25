-- Prove2me | solution 1 for coordFunOfDet_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:09:43.620011+00:00
-- url     : https://prove2.me/submissions/1a9a61dc-2a34-40be-95a6-7df30b2d37e0

module
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Instances.Matrix
public import Definitions.Def_BasicResults_Auerbach
public import Theorems.Thm_coordFunOfDet_apply_eq

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Module FiniteDimensional Metric
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
theorem _root_.solution {n : ℕ} (b₀ : Basis (Fin n) ℝ V)
    (e : Fin n → V) (h_det : b₀.det e ≠ 0) (i j : Fin n) :
    coordFunOfDet b₀ e h_det i (e j) = if i = j then 1 else 0 := by
  rw [coordFunOfDet_apply_eq]
  split_ifs with h
  · subst h; rw [Function.update_eq_self, div_self h_det]
  · rw [div_eq_zero_iff]; left
    exact b₀.det.map_eq_zero_of_eq _
      (by rw [Function.update_self, Function.update_of_ne (Ne.symm h)]) h

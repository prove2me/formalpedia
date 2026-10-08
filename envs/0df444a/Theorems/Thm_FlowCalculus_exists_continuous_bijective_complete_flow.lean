-- Prove2me | Theorems.Thm_FlowCalculus_exists_continuous_bijective_complete_flow
-- name    : FlowCalculus.exists_continuous_bijective_complete_flow
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-06T19:48:27.491535+00:00
-- url     : https://prove2.me/theorems/ee4dd243-6400-4868-ac00-ccbc5fd3cc8f
-- title:
--   Continuous complete flow with smooth trajectories and bijective time maps
-- statement:
--   Let V be a real Banach space and X:ℝ×V→V a smooth vector field with one common compact spatial support. There exists a jointly continuous map ψ:ℝ×V→V such that each trajectory t↦ψ(t,y) is smooth, ψ(0,y)=y, every map ψ(t,·) is bijective, and
--
--   $$ \partial_t\psi(t,y)=X(t,\psi(t,y))\quad(t\in\mathbb R,\ y\in V). $$
--
--   This is a complete ambient flow at the level of joint continuity and smooth trajectories. It does not assert smooth dependence on the initial point, a separate regularity assertion required for a smooth isotopy.
-- source:
--   Completeness and continuity stages of Gray stability, Geiges, Contact geometry, https://arxiv.org/abs/math/0307242, proof of Theorem 2.20, printed p. 15. The proof uses unique complete trajectories and Mathlib.Analysis.ODE.ExistUnique.IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn; timewise regularity uses ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt. Mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474.

import Theorems.Thm_FlowCalculus_uniform_spatial_lipschitz_of_compact_support
import Theorems.Thm_FlowCalculus_exists_unique_global_trajectory_of_compact_support
import Mathlib.Tactic.Linarith

open Set Function Metric
open scoped ContDiff Topology NNReal
set_option autoImplicit false

theorem FlowCalculus.exists_continuous_bijective_complete_flow {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V]
    (X : ℝ → V → V) (hX : ContDiff ℝ ∞ (fun p : ℝ × V => X p.1 p.2))
    (hsupp : ∃ K : Set V, IsCompact K ∧ ∀ t y, y ∉ K → X t y = 0) :
    ∃ ψ : ℝ → V → V, Continuous (fun p : ℝ × V => ψ p.1 p.2) ∧ (∀ y, ContDiff ℝ ∞ (fun t => ψ t y)) ∧ (∀ y, ψ 0 y = y) ∧ (∀ t, Function.Bijective (ψ t)) ∧
      ∀ t y, HasDerivAt (fun s => ψ s y) (X t (ψ t y)) t := by sorry

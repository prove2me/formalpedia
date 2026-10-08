-- Prove2me | Theorems.Thm_FlowCalculus_exists_unique_global_trajectory_of_compact_support
-- name    : FlowCalculus.exists_unique_global_trajectory_of_compact_support
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-06T19:32:48.093832+00:00
-- url     : https://prove2.me/theorems/710f8aa5-a38b-48c5-a63a-6d56ccea6416
-- title:
--   Unique complete trajectory of a smooth uniformly compact-supported field
-- statement:
--   Let V be a real Banach space and X:ℝ×V→V a smooth time-dependent vector field. Assume one compact spatial set contains the support of X(t,·) for every real t. For each initial time t₀ and point x, there is a unique differentiable curve γ:ℝ→V satisfying
--
--   $$ \gamma(t_0)=x,\qquad \gamma'(t)=X(t,\gamma(t))\quad(t\in\mathbb R). $$
--
--   Thus all trajectories are complete, in both time directions. The theorem makes no assertion about joint smoothness in the initial data; that is a separate part of the complete smooth-flow construction.
-- source:
--   Completeness stage of the flow argument in Geiges, Contact geometry, https://arxiv.org/abs/math/0307242, proof of Theorem 2.20, printed p. 15. Uses Mathlib Analysis.ODE.ExistUnique, IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀ and ODE_solution_unique_of_mem_Ioo at commit 0df444a360eaa60ab8c11dca51a86af692955474. Compact-support bounds allow arbitrary finite time intervals; uniqueness glues them into a complete trajectory.

import Theorems.Thm_FlowCalculus_uniform_spatial_lipschitz_of_compact_support
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Tactic.Linarith

open Set
open scoped ContDiff Topology NNReal
set_option autoImplicit false

theorem FlowCalculus.exists_unique_global_trajectory_of_compact_support {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V]
    (X : ℝ → V → V) (hX : ContDiff ℝ ∞ (fun p : ℝ × V => X p.1 p.2))
    (hsupp : ∃ K : Set V, IsCompact K ∧ ∀ t y, y ∉ K → X t y = 0)
    (t₀ : ℝ) (x : V) :
    ∃! γ : ℝ → V, γ t₀ = x ∧ ∀ t, HasDerivAt γ (X t (γ t)) t := by sorry

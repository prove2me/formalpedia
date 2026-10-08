-- Prove2me | Theorems.Thm_FlowCalculus_regular_level_trajectory_invariant
-- name    : FlowCalculus.regular_level_trajectory_invariant
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-06T20:21:56.399227+00:00
-- url     : https://prove2.me/theorems/16d7a321-5899-4532-be4f-dad4dce47d91
-- title:
--   A smooth tangent vector field preserves a regular level along trajectories
-- statement:
--   Let V be a real Banach space and W a finite-dimensional real normed space. Let F:V→W and X:ℝ×V→V be smooth, with DF(y) surjective whenever F(y)=0. Assume DF(y)[X(t,y)]=0 for every t in [a,b] and every y in F⁻¹(0). If γ is continuous on [a,b], satisfies γ′(t)=X(t,γ(t)) for a≤t<b, and F(γ(a))=0, then F(γ(t))=0 for every t in [a,b]. No compactness of the level set, compact support of the field, or smooth dependence on initial states is assumed.
-- source:
--   Regular-level invariance by local implicit-function retraction and Grönwall inequality. An independent Banach-space generalization of the flow-integration step in Geiges, Contact geometry, https://arxiv.org/abs/math/0307242, Theorem 2.20, printed pp. 14–15. Uses Mathlib.Analysis.ODE.Gronwall at commit 0df444a360eaa60ab8c11dca51a86af692955474.

import Theorems.Thm_ImplicitCalculus_local_constraint_residual_bound
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

open Set Filter
open scoped Topology NNReal ContDiff
set_option autoImplicit false

theorem FlowCalculus.regular_level_trajectory_invariant
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (F : V → W) (hF : ContDiff ℝ ∞ F)
    (hreg : ∀ y, F y = 0 → Function.Surjective (fderiv ℝ F y))
    (X : ℝ → V → V) (hX : ContDiff ℝ ∞ (fun p : ℝ × V => X p.1 p.2))
    (a b : ℝ) (htan : ∀ t ∈ Icc a b, ∀ y, F y = 0 → fderiv ℝ F y (X t y) = 0)
    (γ : ℝ → V) (hc : ContinuousOn γ (Icc a b))
    (hd : ∀ t ∈ Ico a b, HasDerivAt γ (X t (γ t)) t)
    (h0 : F (γ a) = 0) : ∀ t ∈ Icc a b, F (γ t) = 0 := by sorry

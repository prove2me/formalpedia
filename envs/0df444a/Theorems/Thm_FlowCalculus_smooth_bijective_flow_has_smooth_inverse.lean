-- Prove2me | Theorems.Thm_FlowCalculus_smooth_bijective_flow_has_smooth_inverse
-- name    : FlowCalculus.smooth_bijective_flow_has_smooth_inverse
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-06T22:02:32.093155+00:00
-- url     : https://prove2.me/theorems/57d4d0ee-535e-4130-86c9-331ce41da318
-- title:
--   Smooth inverse time maps of a smooth bijective flow
-- statement:
--   Let V be a finite-dimensional real normed space, and let X and ψ be jointly smooth. Suppose ψ(0,y)=y, every ψ(t,·) is bijective, and ∂ₜψ(t,y)=X(t,ψ(t,y)) everywhere. There is a family ρ of smooth inverse maps satisfying ρ(t,ψ(t,y))=y and ψ(t,ρ(t,y))=y for all real t and y. Smoothness is asserted for each spatial inverse map; joint smooth dependence of the given flow is an explicit hypothesis.
-- source:
--   Variational equation, linear ODE uniqueness, and the inverse function theorem. Independent formulation for the flow-integration step of Geiges, Contact geometry, https://arxiv.org/abs/math/0307242, Theorem 2.20, pp. 14–15. Uses the independently proved first variational equation, Mathlib.Analysis.ODE.ExistUnique.ODE_solution_unique_of_mem_Ioo and Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff.to_localInverse, commit 0df444a360eaa60ab8c11dca51a86af692955474.

import Theorems.Thm_FlowCalculus_smooth_flow_spatial_derivative_injective
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

open Set Function
open scoped ContDiff Topology NNReal
set_option autoImplicit false

theorem FlowCalculus.smooth_bijective_flow_has_smooth_inverse
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (X ψ : ℝ → V → V)
    (hX : ContDiff ℝ ∞ (fun p : ℝ × V => X p.1 p.2))
    (hψ : ContDiff ℝ ∞ (fun p : ℝ × V => ψ p.1 p.2))
    (h0 : ∀ y, ψ 0 y = y) (hb : ∀ t, Bijective (ψ t))
    (hd : ∀ t y, HasDerivAt (fun s => ψ s y) (X t (ψ t y)) t) :
    ∃ ρ : ℝ → V → V, (∀ t, ContDiff ℝ ∞ (ρ t)) ∧
      (∀ t y, ρ t (ψ t y) = y) ∧ (∀ t y, ψ t (ρ t y) = y) := by sorry

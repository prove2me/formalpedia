-- Prove2me | Theorems.Thm_FlowCalculus_smooth_flow_spatial_derivative_injective
-- name    : FlowCalculus.smooth_flow_spatial_derivative_injective
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-06T21:59:55.414355+00:00
-- url     : https://prove2.me/theorems/2d213970-6d27-4810-9c20-915502749805
-- title:
--   The spatial differential of a smooth complete flow is injective
-- statement:
--   Let V be a real Banach space, and let X and ψ be jointly smooth maps from ℝ×V to V. Suppose ψ(0,y)=y and ∂ₜψ(t,y)=X(t,ψ(t,y)) for all t,y. Then Dᵧψ(t,y) is injective for every t and y. No compact support or bijectivity assumption is needed.
-- source:
--   Variational equation, linear ODE uniqueness, and the inverse function theorem. Independent formulation for the flow-integration step of Geiges, Contact geometry, https://arxiv.org/abs/math/0307242, Theorem 2.20, pp. 14–15. Uses the independently proved first variational equation, Mathlib.Analysis.ODE.ExistUnique.ODE_solution_unique_of_mem_Ioo and Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff.to_localInverse, commit 0df444a360eaa60ab8c11dca51a86af692955474.

import Theorems.Thm_FlowCalculus_spatial_differential_hasDerivAt
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.Linarith

open Set Function
open scoped ContDiff Topology NNReal
set_option autoImplicit false

theorem FlowCalculus.smooth_flow_spatial_derivative_injective
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (X ψ : ℝ → V → V)
    (hX : ContDiff ℝ ∞ (fun p : ℝ × V => X p.1 p.2))
    (hψ : ContDiff ℝ ∞ (fun p : ℝ × V => ψ p.1 p.2))
    (h0 : ∀ y, ψ 0 y = y)
    (hd : ∀ t y, HasDerivAt (fun s => ψ s y) (X t (ψ t y)) t) :
    ∀ t y, Injective (fderiv ℝ (ψ t) y) := by sorry

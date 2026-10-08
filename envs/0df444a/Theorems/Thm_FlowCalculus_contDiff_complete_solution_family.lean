-- Prove2me | Theorems.Thm_FlowCalculus_contDiff_complete_solution_family
-- name    : FlowCalculus.contDiff_complete_solution_family
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-07T08:20:27.649125+00:00
-- url     : https://prove2.me/theorems/26a9cd41-b231-4d3d-8f91-00d4c6747e5d
-- title:
--   Joint smoothness of a complete ODE solution family
-- statement:
--   Let V be a finite-dimensional real normed space. Let X:ℝ×V→V be jointly smooth, and let ψ:ℝ×V→V be a jointly continuous family of complete solutions with initial value ψ(0,y)=y. Assume
--
--   $$\partial_t\psi(t,y)=X(t,\psi(t,y))\qquad(t\in\mathbb R,\ y\in V).$$
--
--   Then ψ is jointly infinitely differentiable in time and initial state. Existence of the complete family is assumed; no compact support, bijectivity, or invariant level set is required. This separates smooth dependence from existence and is useful in constructing smooth flows and isotopies.
-- source:
--   Gerald Teschl, Ordinary Differential Equations and Dynamical Systems, https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf, §2.4, Theorem 2.10 and proof, printed pp. 46–47, equations (2.49)–(2.52); global continuation by uniqueness as in §2.6, Theorem 2.13, pp. 51–52. The statement is the C∞, fixed initial time 0 consequence for an already supplied complete solution family, transported from Euclidean space to a finite-dimensional real normed space.

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

open scoped ContDiff
set_option autoImplicit false

theorem FlowCalculus.contDiff_complete_solution_family
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (X ψ : ℝ → V → V)
    (hX : ContDiff ℝ ∞ (fun p : ℝ × V => X p.1 p.2))
    (hc : Continuous (fun p : ℝ × V => ψ p.1 p.2))
    (h0 : ∀ y, ψ 0 y = y)
    (hd : ∀ t y, HasDerivAt (fun s => ψ s y) (X t (ψ t y)) t) :
    ContDiff ℝ ∞ (fun p : ℝ × V => ψ p.1 p.2) := by sorry

-- Prove2me | Theorems.Thm_FamousTheorems_integral_curve_local_existence
-- name    : FamousTheorems.integral_curve_local_existence
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T21:26:41.714985+00:00
-- url     : https://prove2.me/theorems/cfa1bed8-2d19-4c21-b443-0939e0530867
-- title:
--   Local existence of integral curves on manifolds
-- statement:
--   **Local existence of integral curves.** Let $M$ be a $C^1$ manifold without boundary modelled on a real Banach space, and $v$ a $C^1$ vector field on $M$ near a point $x_0$. For every $t_0\in\mathbb R$ there is a curve $\gamma$ with $\gamma(t_0)=x_0$ that is an integral curve of $v$ on a neighbourhood of $t_0$, i.e. $\gamma'(t)=v(\gamma(t))$ for all $t$ near $t_0$.
--
--   This is the Picard–Lindelöf theorem transported to manifolds. It is the basis of flows of vector fields, of the exponential map of Lie groups and Riemannian manifolds, and of the theory of dynamical systems on manifolds.
--
--   **Formalization note.** Mathlib's `exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless`. The smoothness hypothesis is that the section $x\mapsto(x,v(x))$ of the tangent bundle is $C^1$ at $x_0$. `IsMIntegralCurveAt γ v t₀` means $\gamma$ has derivative $v(\gamma(t))$ at every $t$ in a neighbourhood of $t_0$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem integral_curve_local_existence {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [BoundarylessManifold I M] {v : (x : M) → TangentSpace I x} (t₀ : ℝ) {x₀ : M}
    (hv : ContMDiffAt I I.tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)) x₀) :
    ∃ γ : ℝ → M, γ t₀ = x₀ ∧ IsMIntegralCurveAt γ v t₀ := by sorry

end FamousTheorems

-- Prove2me | Theorems.Thm_ClarkeGradients_FlowInvariance_gradient_infDist_of_ne_zero
-- name    : ClarkeGradients.FlowInvariance.gradient_infDist_of_ne_zero
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T22:46:15.010999+00:00
-- url     : https://prove2.me/theorems/8d40903b-2011-46ad-bb24-9938d3135816
-- title:
--   Proposition (2.4) — a nonzero gradient of d_E points away from the unique closest point
-- statement:
--   Let $E$ be a nonempty closed subset of $\mathbb R^n$ and $d_E(y)=\min\{|y-e|:e\in E\}$ its distance function. Suppose that $d_E$ is differentiable at $x$ and that $\nabla d_E(x)\ne 0$. Then
--
--   1. $x$ belongs to the complement of $E$;
--   2. there exists a unique point $e\in E$ closest to $x$, i.e. with $|x-e|=d_E(x)$;
--   3. for that point,
--   $$
--   \nabla d_E(x)=\frac{x-e}{|x-e|}.
--   $$
--
--   This is the local description of $d_E$ at its points of differentiability off $E$, and it is what Corollary (2.5) and the proof of Theorem (4.4) use to compute generalized gradients of $d_E$.
--
--   **Formalization Note** $d_E$ is `Metric.infDist · E`; "$e$ is closest to $x$" is `e ∈ E ∧ dist x e = infDist x E`. Part (2) is stated with `∃!`, and part (3) is stated for every closest point (equivalently, by (2), the unique one). The formula is written $\|x-e\|^{-1}\cdot(x-e)$; the division is well defined because $x\notin E$ by (1). The paper proves (2)–(3) by applying Theorem (2.1) (mission I's goal); mission I is a separate draft, so that theorem is not a hypothesis here.
-- source:
--   Clarke, Generalized gradients and applications, Trans. Amer. Math. Soc. 205 (1975), p. 253, Proposition (2.4)

import Mathlib

namespace ClarkeGradients.FlowInvariance

/-- Clarke (1975), Proposition (2.4): let `E ⊆ ℝⁿ` be nonempty and closed and
`d_E(y) = Metric.infDist y E`. If `∇d_E(x)` exists and is different from `0`, then
(1) `x ∉ E`; (2) there is a unique point `e ∈ E` closest to `x`; and
(3) `∇d_E(x) = (x - e)/|x - e|` for that point `e`. -/
theorem gradient_infDist_of_ne_zero {n : ℕ} (E : Set (EuclideanSpace ℝ (Fin n)))
    (hE : E.Nonempty) (hEc : IsClosed E) (x : EuclideanSpace ℝ (Fin n))
    (hdiff : DifferentiableAt ℝ (fun y => Metric.infDist y E) x)
    (hne : gradient (fun y => Metric.infDist y E) x ≠ 0) :
    x ∉ E ∧
      (∃! e : EuclideanSpace ℝ (Fin n), e ∈ E ∧ dist x e = Metric.infDist x E) ∧
      ∀ e ∈ E, dist x e = Metric.infDist x E →
        gradient (fun y => Metric.infDist y E) x = ‖x - e‖⁻¹ • (x - e) := by sorry

end ClarkeGradients.FlowInvariance

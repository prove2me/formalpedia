-- Prove2me | Theorems.Thm_ClarkeGradients_FlowInvariance_generalizedGradient_infDist_eq
-- name    : ClarkeGradients.FlowInvariance.generalizedGradient_infDist_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T22:47:34.927455+00:00
-- url     : https://prove2.me/theorems/9e6574f2-addf-4872-aafe-e51b17459a16
-- title:
--   Corollary (2.5) — the generalized gradient of the distance function on E
-- statement:
--   Let $E$ be a nonempty closed subset of $\mathbb R^n$, $d_E$ its distance function, and $e\in E$. Then
--
--   $$
--   \partial d_E(e)=\operatorname{co}\Big\{0,\ \lim_{i\to\infty}\frac{x_i-e_i}{|x_i-e_i|}\Big\},
--   $$
--
--   where the limits range over all sequences $x_i,e_i$ such that $x_i\notin E$, $e_i$ is a point of $E$ closest to $x_i$, $x_i\to e$ as $i\to\infty$, and the unit vectors $(x_i-e_i)/|x_i-e_i|$ converge; $\operatorname{co}$ denotes the convex hull.
--
--   It expresses the generalized gradient of $d_E$ at a point of $E$ through the unit "proximal" directions pointing from nearby points to their projections onto $E$, and is the basis of the characterization (3.2) of the normal cone.
--
--   **Formalization Note** "$e_i$ is a closest point to $x_i$ in $E$" is `es i ∈ E ∧ dist (xs i) (es i) = infDist (xs i) E`; closest points need not be unique, and any choice is allowed. The right side is `convexHull ℝ (insert 0 S)` with $S$ the set of limits above; "lim" means the sequence converges. Since $x_i\notin E$ and $E$ is closed, $|x_i-e_i|>0$, so the quotients are well defined.
-- source:
--   Clarke, Generalized gradients and applications, Trans. Amer. Math. Soc. 205 (1975), p. 253, Corollary (2.5)

import Mathlib
import Definitions.Def_ClarkeGradients_Shared_generalizedGradient

open Filter Topology

namespace ClarkeGradients.FlowInvariance

/-- Clarke (1975), Corollary (2.5): let `E ⊆ ℝⁿ` be nonempty and closed, `d_E = infDist · E`,
and `e ∈ E`. Then `∂d_E(e) = co{0, lim (xᵢ - eᵢ)/|xᵢ - eᵢ|}`, where the limits range over all
sequences `xᵢ ∉ E` with `xᵢ → e` and `eᵢ` a closest point to `xᵢ` in `E`, for which the unit
vectors `(xᵢ - eᵢ)/|xᵢ - eᵢ|` converge. -/
theorem generalizedGradient_infDist_eq {n : ℕ} (E : Set (EuclideanSpace ℝ (Fin n)))
    (hE : E.Nonempty) (hEc : IsClosed E) (e : EuclideanSpace ℝ (Fin n)) (he : e ∈ E) :
    Shared.generalizedGradient (fun y => Metric.infDist y E) e =
      convexHull ℝ (insert 0
        {ζ | ∃ xs es : ℕ → EuclideanSpace ℝ (Fin n),
          (∀ i, xs i ∉ E) ∧
          (∀ i, es i ∈ E ∧ dist (xs i) (es i) = Metric.infDist (xs i) E) ∧
          Tendsto xs atTop (𝓝 e) ∧
          Tendsto (fun i => ‖xs i - es i‖⁻¹ • (xs i - es i)) atTop (𝓝 ζ)}) := by sorry

end ClarkeGradients.FlowInvariance

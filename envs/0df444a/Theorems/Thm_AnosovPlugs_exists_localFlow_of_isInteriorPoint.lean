-- Prove2me | Theorems.Thm_AnosovPlugs_exists_localFlow_of_isInteriorPoint
-- name    : AnosovPlugs.exists_localFlow_of_isInteriorPoint
-- status  : Proved
-- author  : @ebayuser
-- created : 2026-10-03T19:12:07.426971+00:00
-- url     : https://prove2.me/theorems/15dfe5c0-e724-40ac-835f-bee37bdcdae5
-- title:
--   A C¹ vector field has a local flow at every interior point, continuous in the initial point and unique among integral curves that stay in the neighbourhood
-- statement:
--   Let $M$ be a smooth 3-manifold with boundary (modelled on the closed half-space), let $X$ be a C¹ vector field on $M$, and let $x_0$ be an interior point of $M$. An *integral curve of $X$ on a set of times* $S\subseteq\mathbb R$ is a curve $\gamma:\mathbb R\to M$ whose derivative within $S$ at every $u\in S$ is $X(\gamma(u))$ (Mathlib's `IsMIntegralCurveOn`; at the endpoints of an interval the derivative is one-sided). We write $[0,t]$ for the closed interval between $0$ and $t$, in either order (Mathlib's `uIcc 0 t`). Then there are $\varepsilon>0$, an open neighbourhood $O$ of $x_0$ and a map $\alpha:M\to\mathbb R\to M$ (a local flow) such that:
--   1. for every $y\in O$, $\alpha(y,0)=y$, the curve $\alpha(y,\cdot)$ is an integral curve of $X$ on $[-\varepsilon,\varepsilon]$, and $\alpha(y,\tau)$ is an interior point of $M$ for every $\tau\in[-\varepsilon,\varepsilon]$;
--   2. for every $\tau\in[-\varepsilon,\varepsilon]$, the map $y\mapsto\alpha(y,\tau)$ is continuous on $O$;
--   3. (uniqueness inside $O$) for every $y\in O$, every $h$ with $|h|\le\varepsilon$ and every integral curve $\eta$ of $X$ on $[0,h]$ with $\eta(0)=y$ and $\eta([0,h])\subseteq O$, one has
--      $$ \eta(\tau)=\alpha(y,\tau)\quad\text{for all } \tau\in[0,h]. $$
--
--   In words: near an interior point, a C¹ vector field has a local flow defined for a uniform short time, continuous in the initial point, and unique among integral curves that stay in the neighbourhood. This is the Picard–Lindelöf theorem with parameters, read in a chart at $x_0$. A general fact of ordinary differential equations, not stated in the paper; it is used tacitly in the proof of Proposition 1.1 (Section 3.1 of arXiv v1, p. 14), whose fourth and fifth sentences use, without comment, that the flow of the glued vector field Z near the maximal invariant set Λ_X of the plug (U, X) is the flow of X. In the proof of the companion statement `exists_integralCurveOn_nhds` it is the local building block that is iterated along a compact orbit segment.
--
--   **Formalization Note** No Hausdorff hypothesis is assumed: the uniqueness clause is restricted to curves that stay in $O$; the statement does not say that $O$ lies in one chart, but a proof may choose $O$ inside one chart, and then the clause follows from uniqueness for Lipschitz ordinary differential equations in $\mathbb R^3$; this is why the clause carries the hypothesis $\eta([0,h])\subseteq O$. Continuity in the initial point is stated for each fixed time $\tau$ separately, which is all the companion statement needs. Mathlib (at the pinned version) has the chart-level local flow (`IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn`) and short-time existence on manifolds (`exists_isMIntegralCurveAt_of_contMDiffAt`), but no local flow on manifolds. C¹ is the mission's `IsC1VectorField`.
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837 (arXiv:1408.3951v1). A general fact of ordinary differential equations, not stated in the paper; it is used tacitly in the proof of Proposition 1.1 (Section 3.1 of arXiv v1, p. 14), whose fourth and fifth sentences use, without comment, that the flow of the glued vector field Z near the maximal invariant set Λ_X of the plug (U, X) is the flow of X. Textbook fact (Picard–Lindelöf with parameters). Mathlib notions: IsMIntegralCurveOn, ModelWithCorners.IsInteriorPoint, IsPicardLindelof; mission notion: IsC1VectorField.

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

theorem exists_localFlow_of_isInteriorPoint
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    (X : (x : M) → TangentSpace I3 x) (hX : IsC1VectorField X)
    (x₀ : M) (hx₀ : I3.IsInteriorPoint x₀) :
    ∃ ε > (0 : ℝ), ∃ O : Set M, IsOpen O ∧ x₀ ∈ O ∧ ∃ α : M → ℝ → M,
      (∀ y ∈ O, α y 0 = y ∧ IsMIntegralCurveOn (α y) X (Icc (-ε) ε) ∧
        ∀ τ ∈ Icc (-ε) ε, I3.IsInteriorPoint (α y τ)) ∧
      (∀ τ ∈ Icc (-ε) ε, ContinuousOn (fun y => α y τ) O) ∧
      (∀ y ∈ O, ∀ h : ℝ, |h| ≤ ε → ∀ η : ℝ → M, η 0 = y →
        IsMIntegralCurveOn η X (uIcc 0 h) → (∀ τ ∈ uIcc 0 h, η τ ∈ O) →
        ∀ τ ∈ uIcc 0 h, η τ = α y τ) := by sorry

end AnosovPlugs

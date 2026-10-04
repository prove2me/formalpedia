-- Prove2me | Theorems.Thm_AnosovPlugs_exists_integralCurveOn_nhds_of_localFlow
-- name    : AnosovPlugs.exists_integralCurveOn_nhds_of_localFlow
-- status  : Proved
-- author  : @ebayuser
-- created : 2026-10-03T19:12:12.73291+00:00
-- url     : https://prove2.me/theorems/347c5b34-6f0f-42b4-a6c3-d1b3753805ce
-- title:
--   Local flows at interior points iterate along a compact orbit segment: nearby initial points have integral curves on the whole interval
-- statement:
--   Let $M$ be a smooth 3-manifold with boundary (modelled on the closed half-space) and let $X$ be a vector field on $M$ that has local flows at interior points: for every interior point $x_0$ there are $\varepsilon>0$, an open neighbourhood $O$ of $x_0$ and $\alpha:M\to\mathbb R\to M$ with the three properties of the companion statement `exists_localFlow_of_isInteriorPoint` (integral curves on $[-\varepsilon,\varepsilon]$ through interior points starting at every $y\in O$, continuity in $y$ for each fixed time, and uniqueness among integral curves that stay in $O$). An *integral curve of $X$ on a set of times* $S\subseteq\mathbb R$ is a curve $\gamma:\mathbb R\to M$ whose derivative within $S$ at every $u\in S$ is $X(\gamma(u))$ (Mathlib's `IsMIntegralCurveOn`; at the endpoints of an interval the derivative is one-sided). We write $[0,t]$ for the closed interval between $0$ and $t$, in either order (Mathlib's `uIcc 0 t`). Let $\gamma$ be an integral curve of $X$ on $[0,t]$ all of whose points $\gamma(s)$, $s\in[0,t]$, are interior points of $M$. Then every point $y$ in some neighbourhood of $\gamma(0)$ is the starting point of an integral curve of $X$ on $[0,t]$ through interior points: for all $y$ near $\gamma(0)$,
--   $$ \exists\,\gamma':\mathbb R\to M,\qquad \gamma'(0)=y,\quad \gamma' \text{ is an integral curve of } X \text{ on } [0,t],\quad \gamma'(s) \text{ is an interior point of } M \text{ for } s\in[0,t]. $$
--
--   In words: local flows at interior points can be iterated along a compact orbit segment: subdivide $[0,t]$ by a Lebesgue number into pieces $[t_k,t_{k+1}]$ each of which lies in the time window of the local flow at some point $\gamma(c_k)$ of the segment and is mapped by $\gamma$ into the neighbourhood $O$ of that local flow, follow nearby initial points piece by piece (the uniqueness clause identifies the local flow of $\gamma(c_k)$, started at the left endpoint $\gamma(t_k)$ of the piece, with $\gamma$ itself, and continuity in the initial point keeps the endpoints close), and glue the pieces. A general fact of ordinary differential equations, not stated in the paper; it is used tacitly in the proof of Proposition 1.1 (Section 3.1 of arXiv v1, p. 14), whose fourth and fifth sentences use, without comment, that the flow of the glued vector field Z near the maximal invariant set Λ_X of the plug (U, X) is the flow of X. Together with `exists_localFlow_of_isInteriorPoint` it proves the companion statement `exists_integralCurveOn_nhds`.
--
--   **Formalization Note** The hypothesis `hflow` is, word for word, the conclusion of `exists_localFlow_of_isInteriorPoint`, quantified over all interior points; the vector field is not assumed C¹ here because only `hflow` is used. No Hausdorff or compactness hypothesis is assumed. The conclusion is stated with Mathlib's `∀ᶠ y in 𝓝 (γ 0)`.
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837 (arXiv:1408.3951v1). A general fact of ordinary differential equations, not stated in the paper; it is used tacitly in the proof of Proposition 1.1 (Section 3.1 of arXiv v1, p. 14), whose fourth and fifth sentences use, without comment, that the flow of the glued vector field Z near the maximal invariant set Λ_X of the plug (U, X) is the flow of X. Textbook fact (continuation of local flows). Mathlib notions: IsMIntegralCurveOn, ModelWithCorners.IsInteriorPoint, Filter.Eventually; companion statement exists_localFlow_of_isInteriorPoint.

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

theorem exists_integralCurveOn_nhds_of_localFlow
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    (X : (x : M) → TangentSpace I3 x)
    (hflow : ∀ x₀ : M, I3.IsInteriorPoint x₀ →
      ∃ ε > (0 : ℝ), ∃ O : Set M, IsOpen O ∧ x₀ ∈ O ∧ ∃ α : M → ℝ → M,
        (∀ y ∈ O, α y 0 = y ∧ IsMIntegralCurveOn (α y) X (Icc (-ε) ε) ∧
          ∀ τ ∈ Icc (-ε) ε, I3.IsInteriorPoint (α y τ)) ∧
        (∀ τ ∈ Icc (-ε) ε, ContinuousOn (fun y => α y τ) O) ∧
        (∀ y ∈ O, ∀ h : ℝ, |h| ≤ ε → ∀ η : ℝ → M, η 0 = y →
          IsMIntegralCurveOn η X (uIcc 0 h) → (∀ τ ∈ uIcc 0 h, η τ ∈ O) →
          ∀ τ ∈ uIcc 0 h, η τ = α y τ))
    (γ : ℝ → M) (t : ℝ)
    (hγ : IsMIntegralCurveOn γ X (uIcc 0 t)) (hint : ∀ s ∈ uIcc 0 t, I3.IsInteriorPoint (γ s)) :
    ∀ᶠ y in 𝓝 (γ 0), ∃ γ' : ℝ → M, γ' 0 = y ∧ IsMIntegralCurveOn γ' X (uIcc 0 t) ∧
      ∀ s ∈ uIcc 0 t, I3.IsInteriorPoint (γ' s) := by sorry

end AnosovPlugs

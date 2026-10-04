-- Prove2me | Theorems.Thm_AnosovPlugs_normalCoord_nonneg_of_hasMFDerivWithinAt
-- name    : AnosovPlugs.normalCoord_nonneg_of_hasMFDerivWithinAt
-- status  : Proved
-- author  : @ebayuser
-- created : 2026-10-02T22:56:44.828466+00:00
-- url     : https://prove2.me/theorems/7128cb5c-77b0-4010-a79c-3ff21f1b471e
-- title:
--   A curve leaving a boundary point of a manifold with boundary has a velocity that does not point outward
-- statement:
--   Let $M$ be a smooth 3-manifold with boundary, modelled on the closed half-space $\{x_0\ge 0\}$, and let $\gamma:\mathbb R\to M$ be a curve that has, within a set of times $s\subseteq\mathbb R$, the derivative $v\in T_{\gamma(t_0)}M$ at the time $t_0$. Assume that $\gamma(t_0)$ is a boundary point of $M$. Let $c$ be a real number in the positive tangent cone of $s$ at $t_0$: a limit of products $a_n d_n$ with $a_n\ge 0$, $d_n\to 0$ and $t_0+d_n\in s$. For $s\subseteq\mathbb R$ this cone is empty when $t_0$ is not in the closure of $s$, and otherwise it is $\{0\}$, $[0,\infty)$, $(-\infty,0]$ or $\mathbb R$ according as $s$ accumulates at $t_0$ from neither side, only from the right, only from the left, or from both sides (for example $c=t_1-t_0$ when $[t_0,t_1]\subseteq s$, or $c=t_1-t_0<0$ when $[t_1,t_0]\subseteq s$). Write $v_0$ for the normal coordinate of $v$: the first coordinate of $v$ in the chart at $\gamma(t_0)$, positive for vectors that point strictly into $M$. Then
--   $$ 0\ \le\ c\,v_0. $$
--
--   In words: a curve that moves from a boundary point into the manifold has a velocity that does not point outward. For an integral curve of a vector field $X$ defined on $[t_0,t_1]$ with $t_0<t_1$ and starting at a boundary point, the normal coordinate of $X(\gamma(t_0))$ is nonnegative; for one defined on $[t_1,t_0]$ with $t_1<t_0$ and ending at a boundary point, it is nonpositive. This is the fact behind one inclusion in the sentences of Definitions 2.1: a point whose forward orbit is defined forever has a positive orbit disjoint from $\partial^{out}V$, and a point whose backward orbit is defined forever has a negative orbit disjoint from $\partial^{in}V$.
--
--   **Formalization Note** The hypothesis on the derivative is Mathlib's `HasMFDerivWithinAt` for the curve, with the derivative written as the linear map $r\mapsto r\,v$; the direction $c$ is an element of Mathlib's `posTangentConeAt s t_0`. The two interval cases above are instances, obtained from `mem_posTangentConeAt_of_segment_subset`. The normal coordinate is the mission's `normalCoord`.
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837 (arXiv:1408.3951v1). Definitions 2.1 of arXiv v1 (p. 7): 'The stable set W^s(Λ) is the set of points whose forward orbit is defined forever. Equivalently, [...] is the set of points whose positive orbit is disjoint from ∂^out V. Analogously the unstable set W^u(Λ) is the set of points whose backward orbit is defined forever; this negative orbit is disjoint from ∂^in V.' (Definitions 3.1 in the published version.) The statement is the one-sided derivative fact behind these sentences; Mathlib notions: HasMFDerivWithinAt, posTangentConeAt, ModelWithCorners.boundary.

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

theorem normalCoord_nonneg_of_hasMFDerivWithinAt
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    (γ : ℝ → M) (s : Set ℝ) (t₀ : ℝ) (v : TangentSpace I3 (γ t₀))
    (hγ : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I3 γ s t₀ ((1 : ℝ →L[ℝ] ℝ).smulRight v))
    (hb : γ t₀ ∈ I3.boundary M) (c : ℝ) (hc : c ∈ posTangentConeAt s t₀) :
    0 ≤ c * normalCoord v := by sorry

end AnosovPlugs

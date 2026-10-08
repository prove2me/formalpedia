-- Prove2me | Theorems.Thm_AnosovPlugs_localSteps_of_embedding
-- name    : AnosovPlugs.localSteps_of_embedding
-- status  : Proved
-- author  : @ebayuser
-- created : 2026-10-04T20:35:47.280071+00:00
-- url     : https://prove2.me/theorems/56a368bf-796a-42f7-8bb2-d547bb8c643b
-- title:
--   A C¹ map with injective derivative at an interior point carries a C¹ local flow to C¹ short-time flow maps of the pushed vector field
-- statement:
--   Let $M$ and $N$ be smooth 3-manifolds with boundary (modelled on the closed half-space), let $i:M\to N$ be a map of class C¹, and let $X$ and $Z$ be vector fields on $M$ and $N$ with $Di_x(X(x))=Z(i(x))$ for all $x\in M$. Let $x_0$ be an interior point of $M$ at which the derivative $Di_{x_0}$ is injective. An *integral curve of a vector field $F$ on a manifold $N$ on a set of times* $S\subseteq\mathbb R$ is a curve $\gamma:\mathbb R\to N$ whose derivative within $S$ at every $u\in S$ is $F(\gamma(u))$ (Mathlib's `IsMIntegralCurveOn`; at the endpoints of an interval the derivative is one-sided). We write $[0,t]$ for the closed interval between $0$ and $t$, in either order (Mathlib's `uIcc 0 t`). Assume that $X$ has a jointly C¹ local flow at $x_0$: there are $\varepsilon>0$, an open neighbourhood $O$ of $x_0$ and a map $\alpha:M\to\mathbb R\to M$ such that for every $y\in O$ the curve $\alpha(y,\cdot)$ is an integral curve of $X$ on $[-\varepsilon,\varepsilon]$ with $\alpha(y,0)=y$, and $(y,\tau)\mapsto\alpha(y,\tau)$ is of class C¹ on $O\times(-\varepsilon,\varepsilon)$ (the full hypothesis is the conclusion of the companion theorem `exists_localFlow_contMDiff_of_isInteriorPoint`). A vector field $F$ on a 3-manifold $N$ has *local C¹ step maps at a point* $p$ if there are $\varepsilon>0$ and an open neighbourhood $O$ of $p$ such that for every $h$ with $|h|\le\varepsilon$ there is a map $f_h:N\to N$ of class C¹ on $O$ with this property: every $y\in O$ is the starting point of an integral curve $\eta$ of $F$ on $[0,h]$ with $\eta(h)=f_h(y)$. Then
--   $$ Z \text{ has local } C^1 \text{ step maps at } i(x_0). $$
--
--   In words: by the inverse function theorem, $i$ is a C¹ diffeomorphism from a neighbourhood of $x_0$ onto a neighbourhood of $i(x_0)$ (in particular $i(x_0)$ is an interior point of $N$), and it carries the local flow of $X$ to short-time flow maps of $Z$: $f_h=i\circ\alpha(\cdot,h)\circ i^{-1}$. It is a step of the mission's proof of the C¹ regularity that the proof of Proposition 1.1 (Section 3.1 of arXiv v1, p. 14) takes for granted. There $i$ is one of the two embeddings $i_U$, $i_V$ of a plug gluing and $Z$ is the glued field. The statement covers the points of $W$ that are images of interior points of $U$ or $V$.
--
--   **Formalization Note** The hypothesis on the local flow is the verbatim conclusion of `exists_localFlow_contMDiff_of_isInteriorPoint`; its clauses on interior points and on uniqueness are part of that conclusion and are not needed for the expected proof. The derivative of $i$ is assumed injective at $x_0$ only; the tangent spaces are 3-dimensional, so it is bijective. $i$ is not assumed to be an embedding. No Hausdorff and no compactness hypothesis is assumed.
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837 (arXiv:1408.3951v1). General fact (inverse function theorem and transport of a local flow), used tacitly in footnote 2 and in the proof of Proposition 1.1 (arXiv v1 Section 3.1). Mathlib notions: IsMIntegralCurveOn, ModelWithCorners.IsInteriorPoint, mfderiv; companion theorem exists_localFlow_contMDiff_of_isInteriorPoint.

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

theorem localSteps_of_embedding
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    {N : Type} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N] [IsManifold I3 ∞ N]
    (X : (x : M) → TangentSpace I3 x) (Z : (w : N) → TangentSpace I3 w) (i : M → N)
    (hi : ContMDiff I3 I3 1 i)
    (hZ : ∀ x, mfderiv I3 I3 i x (X x) = Z (i x))
    (x₀ : M) (hx₀ : I3.IsInteriorPoint x₀) (hinj : Function.Injective (mfderiv I3 I3 i x₀))
    (hflow : ∃ ε > (0 : ℝ), ∃ O : Set M, IsOpen O ∧ x₀ ∈ O ∧ ∃ α : M → ℝ → M,
        (∀ y ∈ O, α y 0 = y ∧ IsMIntegralCurveOn (α y) X (Icc (-ε) ε) ∧
          ∀ τ ∈ Icc (-ε) ε, I3.IsInteriorPoint (α y τ)) ∧
        ContMDiffOn (I3.prod 𝓘(ℝ, ℝ)) I3 1 (fun p : M × ℝ => α p.1 p.2) (O ×ˢ Ioo (-ε) ε) ∧
        (∀ y ∈ O, ∀ h : ℝ, |h| ≤ ε → ∀ η : ℝ → M, η 0 = y →
          IsMIntegralCurveOn η X (uIcc 0 h) → (∀ τ ∈ uIcc 0 h, η τ ∈ O) →
          ∀ τ ∈ uIcc 0 h, η τ = α y τ)) :
    ∃ ε > (0 : ℝ), ∃ O : Set N, IsOpen O ∧ i x₀ ∈ O ∧ ∀ h : ℝ, |h| ≤ ε → ∃ f : N → N,
      ContMDiffOn I3 I3 1 f O ∧
      ∀ y ∈ O, ∃ η : ℝ → N, η 0 = y ∧ IsMIntegralCurveOn η Z (uIcc 0 h) ∧ η h = f y := by sorry

end AnosovPlugs

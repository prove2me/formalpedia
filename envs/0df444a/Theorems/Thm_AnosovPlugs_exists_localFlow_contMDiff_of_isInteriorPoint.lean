-- Prove2me | Theorems.Thm_AnosovPlugs_exists_localFlow_contMDiff_of_isInteriorPoint
-- name    : AnosovPlugs.exists_localFlow_contMDiff_of_isInteriorPoint
-- status  : Proved
-- author  : @ebayuser
-- created : 2026-10-03T20:57:56.757005+00:00
-- url     : https://prove2.me/theorems/65359750-62a4-4d30-b22f-2b880eed54f5
-- title:
--   A C¹ vector field has a local flow at every interior point that is jointly C¹ in the initial point and the time
-- statement:
--   Let $M$ be a smooth 3-manifold with boundary (modelled on the closed half-space), let $X$ be a C¹ vector field on $M$, and let $x_0$ be an interior point of $M$. An *integral curve of $X$ on a set of times* $S\subseteq\mathbb R$ is a curve $\gamma:\mathbb R\to M$ whose derivative within $S$ at every $u\in S$ is $X(\gamma(u))$ (Mathlib's `IsMIntegralCurveOn`; at the endpoints of an interval the derivative is one-sided). We write $[0,t]$ for the closed interval between $0$ and $t$, in either order (Mathlib's `uIcc 0 t`). Then there are $\varepsilon>0$, an open neighbourhood $O$ of $x_0$ and a map $\alpha:M\to\mathbb R\to M$ (a local flow) such that:
--   1. for every $y\in O$, $\alpha(y,0)=y$, the curve $\alpha(y,\cdot)$ is an integral curve of $X$ on $[-\varepsilon,\varepsilon]$, and $\alpha(y,\tau)$ is an interior point of $M$ for every $\tau\in[-\varepsilon,\varepsilon]$;
--   2. the map $(y,\tau)\mapsto\alpha(y,\tau)$ is of class C¹ on the open set $O\times(-\varepsilon,\varepsilon)$ of the product manifold $M\times\mathbb R$;
--   3. (uniqueness inside $O$) for every $y\in O$, every $h$ with $|h|\le\varepsilon$ and every integral curve $\eta$ of $X$ on $[0,h]$ with $\eta(0)=y$ and $\eta([0,h])\subseteq O$, one has
--      $$ \eta(\tau)=\alpha(y,\tau)\quad\text{for all } \tau\in[0,h]. $$
--
--   In words: near an interior point, a C¹ vector field has a local flow that is jointly C¹ in the initial point and the time (differentiable dependence on initial conditions; see Hartman, *Ordinary Differential Equations*, Chapter V). This strengthens the proved theorem `exists_localFlow_of_isInteriorPoint`, whose second clause asks only continuity in $y$ for each fixed time. It is used in the proof of Proposition 1.1 (Section 3.1 of arXiv v1, p. 14; GT 2017 Section 4.1). There it gives C¹ time-$t$ maps of $X$ and $Y$ near orbits that stay in the interior of $U$ or $V$. It does not reach the boundary. Near the seam the time-$t$ maps of $Z$ also need a C¹ flow of $X$ up to $T^{out}$ and of $Y$ up to $T^{in}$. That part is not in this statement.
--
--   **Formalization Note** Clause 2 is `ContMDiffOn (I3.prod 𝓘(ℝ, ℝ)) I3 1 (fun p => α p.1 p.2) (O ×ˢ Ioo (-ε) ε)` on the product manifold $M\times\mathbb R$; the open product is used so that clause 2 is a C¹ statement on an open subset of $M\times\mathbb R$. Clauses 1 and 3 are those of `exists_localFlow_of_isInteriorPoint`. No Hausdorff hypothesis is assumed. Mathlib (at the pinned version) has no differentiable dependence of solutions of ordinary differential equations on initial conditions, in Banach spaces or on manifolds. The proof in this mission goes through the companion theorems `contDiffOn_fixedPoint_of_contraction`, `contDiff_continuousMap_comp_left`, `exists_flow_contDiffOn_of_lipschitz` and `exists_localFlow_contDiffOn_of_contDiffAt`.
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837 (arXiv:1408.3951v1). Textbook ODE theory (differentiable dependence on initial conditions: Hartman, Ordinary Differential Equations, Ch. V), used tacitly in the proof of Proposition 1.1 (arXiv v1 Section 3.1, GT 2017 Section 4.1). Mathlib notions: IsMIntegralCurveOn, ModelWithCorners.IsInteriorPoint, ContMDiffOn on the product manifold; mission notion: IsC1VectorField; companion theorem exists_localFlow_of_isInteriorPoint.

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

theorem exists_localFlow_contMDiff_of_isInteriorPoint
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    (X : (x : M) → TangentSpace I3 x) (hX : IsC1VectorField X)
    (x₀ : M) (hx₀ : I3.IsInteriorPoint x₀) :
    ∃ ε > (0 : ℝ), ∃ O : Set M, IsOpen O ∧ x₀ ∈ O ∧ ∃ α : M → ℝ → M,
      (∀ y ∈ O, α y 0 = y ∧ IsMIntegralCurveOn (α y) X (Icc (-ε) ε) ∧
        ∀ τ ∈ Icc (-ε) ε, I3.IsInteriorPoint (α y τ)) ∧
      ContMDiffOn (I3.prod 𝓘(ℝ, ℝ)) I3 1 (fun p : M × ℝ => α p.1 p.2) (O ×ˢ Ioo (-ε) ε) ∧
      (∀ y ∈ O, ∀ h : ℝ, |h| ≤ ε → ∀ η : ℝ → M, η 0 = y →
        IsMIntegralCurveOn η X (uIcc 0 h) → (∀ τ ∈ uIcc 0 h, η τ ∈ O) →
        ∀ τ ∈ uIcc 0 h, η τ = α y τ) := by sorry

end AnosovPlugs

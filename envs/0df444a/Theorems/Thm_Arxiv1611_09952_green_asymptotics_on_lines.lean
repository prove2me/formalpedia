-- Prove2me | Theorems.Thm_Arxiv1611_09952_green_asymptotics_on_lines
-- name    : Arxiv1611_09952.green_asymptotics_on_lines
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T23:47:55.957805+00:00
-- url     : https://prove2.me/theorems/ebcc575f-9a26-43c1-83ea-df103a509bc8
-- title:
--   Section 2, after Lemma 1: Lemma 1 holds along the lines $y=-\tau\alpha+\eta$
-- statement:
--   Let $k>0$, let $D$ be an obstacle with the Dirichlet condition, $G$ its Dirichlet Green's function, $\alpha\in S^2$, $u(\cdot,\alpha)$ the scattering solution, and $\eta\in\mathbb{R}^3$ with $\eta\cdot\alpha=0$. Put $y(\tau)=-\tau\alpha+\eta$ and $g(r)=e^{ikr}/(4\pi r)$. Then for every $x\in D'$, as $\tau\to\infty$:
--
--   1. Lemma 1 holds along the line: $$G(x,y(\tau))=g(|y(\tau)|)\,u(x,\alpha)+O\Big(\frac1{\tau^2}\Big);$$
--   2. $|y(\tau)|/\tau=1+O(1/\tau^2)$;
--   3. for $\tau>0$, $|y(\tau)|\to\infty$ is equivalent to $\tau\to\infty$;
--   4. $g(|y(\tau)|)=g(\tau)\,(1+O(1/\tau))$.
--
--   This extends Lemma 1, where $y/|y|=-\alpha$ exactly, to lines parallel to $-\alpha$; it is used in Lemma 4 and in the implications (26)-(27).
--
--   **Formalization Note** The remainder in item 1 is written $O(1/\tau^2)$, which is the same as $O(1/|y|^2)$ by item 2. The equivalence in item 3 is written as an equality of filters: the pull-back of $|y|\to\infty$, restricted to $\tau>0$, is $\tau\to\infty$.
-- source:
--   A. G. Ramm, Inverse obstacle scattering with non-over-determined data, arXiv:1611.09952v2 (2017), claim c013; Section 2, paragraph after Lemma 1 (eq. (5)) and the unique continuation property, PDF p. 4

import Mathlib
import Definitions.Def_Arxiv1611_09952_Basic

open MeasureTheory Filter Topology Asymptotics

namespace Arxiv1611_09952

theorem green_asymptotics_on_lines (k : ℝ) (hk : 0 < k) (D : Set E3) (hD : IsObstacle D)
    (G : E3 → E3 → ℂ) (hG : IsDirichletGreen D k G)
    (α : E3) (hα : α ∈ Metric.sphere (0 : E3) 1) (u : E3 → ℂ)
    (hu : IsScatteringSolution D .dirichlet k α u)
    (η : E3) (hη : inner ℝ η α = 0) (x : E3) (hx : x ∈ Dᶜ) :
    (fun τ : ℝ => G x ((-τ) • α + η) - gRad k ‖(-τ) • α + η‖ * u x) =O[atTop]
        (fun τ : ℝ => 1 / τ ^ 2) ∧
    (fun τ : ℝ => ‖(-τ) • α + η‖ / τ - 1) =O[atTop] (fun τ : ℝ => 1 / τ ^ 2) ∧
    Filter.comap (fun τ : ℝ => ‖(-τ) • α + η‖) atTop ⊓ 𝓟 (Set.Ioi 0) = atTop ∧
    (fun τ : ℝ => gRad k ‖(-τ) • α + η‖ / gRad k τ - 1) =O[atTop] (fun τ : ℝ => 1 / τ) := by sorry

end Arxiv1611_09952

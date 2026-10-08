-- Prove2me | Theorems.Thm_AssortSearch_SearchQC_theorem_5
-- name    : AssortSearch.SearchQC.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:31:57.543089+00:00
-- url     : https://prove2.me/theorems/b88dd405-7065-4c61-bbb1-2d98baacce39
-- title:
--   Theorem 5 (common margin): under independent-assortment search, $h^{si}(v_j)=\pi_j^{si}(v_j)-L^{si}(v_j)$ is quasi-convex on $[0,\infty)$
-- statement:
--   Consider the independent-assortment search model of Cachon, Terwiesch and Xu. There are $n$ variants with preferences $v_i>0$ and a no-purchase option with preference $v_0>0$; $\lambda=\exp[-(\bar U/\mu+\gamma)]>0$ is the search parameter; every variant earns the same margin $m\in\mathbb R$; and the operational cost $c$ is concave and increasing on $[0,1]$ and twice continuously differentiable on $(0,1)$. Variant $i$'s demand in an assortment $S$ is
--   $$q_i^{si}(S)=\frac{v_i}{\sum_{k\in S}v_k+v_0}\Bigl(1-e^{-\lambda(v_0+\sum_{k\in S}v_k)}\Bigr),$$
--   and its profit is $\pi_i^{si}(S)=m\,q_i^{si}(S)-c(q_i^{si}(S))$.
--
--   Fix an assortment $S$ and a variant $j\notin S$, and give $j$ a variable preference $v_j\ge0$. Let $\pi_i^{si}(v_j)$ be variant $i$'s profit in $S\cup\{j\}$, let $L^{si}(v_j)=\sum_{i\in S}\pi_i^{si}(S)-\sum_{i\in S}\pi_i^{si}(v_j)$, and let
--   $$h^{si}(v_j)=\pi_j^{si}(v_j)-L^{si}(v_j)$$
--   be the change in total profit from adding $j$. Then $h^{si}$ is quasi-convex on $[0,\infty)$: for all $0\le a\le b$ and $t\in[a,b]$,
--   $$h^{si}(t)\le\max\{h^{si}(a),h^{si}(b)\}.$$
--
--   Quasi-convexity means that adding a variant is most profitable at an extreme of its popularity, which is what places the optimal assortment among the popular assortments, the sets of the $k$ most preferred variants.
--
--   **Formalization Note** The paper's model allows a margin $m_i$ per variant. The theorem is stated with one margin $m$ for every variant, including $j$, as the proof's displays (7)–(9) do; with unequal margins the statement is false (one variant $i\in S$ with $v_i=0.76202736$, $v_0=0.021273423$, $c(q)=0.38165308\,q^{0.59833805}$, $m_j=5.4080321$, $m_i=6.1078441$, $\lambda=2.6494844$ gives an $h^{si}$ that rises, falls and rises again). The paper assumes only "concave and increasing"; twice continuous differentiability on $(0,1)$ is added because the proof uses $c'$ and $c''$. $\lambda>0$ is a free parameter (every real $\bar U$ gives one). Quasi-convexity is Mathlib's `QuasiconvexOn ℝ (Set.Ici 0)`. At $v_j=0$, $h^{si}(0)=-c(0)$.
-- source:
--   Cachon, Terwiesch & Xu, Retail Assortment Planning in the Presence of Consumer Search, working paper (Dec. 20, 2002), p. 14 (PDF 16), Theorem 5

import Mathlib
import Definitions.Def_AssortSearch_SearchQC_Model

namespace AssortSearch.SearchQC

/-- Theorem 5 (p. 14), common-margin case: under independent-assortment search, with one margin
`m` for every variant and a concave, increasing, twice continuously differentiable cost `c`,
`h^si(v_j) = π_j^si(v_j) - L^si(v_j)` is quasi-convex in `v_j` on `[0, ∞)`. `lam` is
`λ = exp[-(Ū/μ + γ)]`, taken as a free positive parameter. -/
theorem theorem_5 {n : ℕ} (v : Fin n → ℝ) (v0 lam m : ℝ) (c : ℝ → ℝ)
    (S : Finset (Fin n)) (j : Fin n)
    (hv : ∀ i, 0 < v i) (hv0 : 0 < v0) (hlam : 0 < lam) (hj : j ∉ S)
    (hconc : ConcaveOn ℝ (Set.Icc 0 1) c) (hmono : MonotoneOn c (Set.Icc 0 1))
    (hsmooth : ContDiffOn ℝ 2 c (Set.Ioo 0 1)) :
    QuasiconvexOn ℝ (Set.Ici 0) (hSI m c lam v v0 S j) := by sorry

end AssortSearch.SearchQC

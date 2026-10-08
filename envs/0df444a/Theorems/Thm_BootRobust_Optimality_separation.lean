-- Prove2me | Theorems.Thm_BootRobust_Optimality_separation
-- name    : BootRobust.Optimality.separation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:09:29.419983+00:00
-- url     : https://prove2.me/theorems/48cbf2d6-3a36-46e1-9a8a-ceedf0182c26
-- title:
--   B.2, p. 27 — a linear functional 𝔼_D[G] separates the R-ball from a convex open set on which R > r
-- statement:
--   Let $R$ be a distribution distance function on $\mathcal D_n$, let $D_{\rm tr}\in\mathcal D_n$ and $r\in\mathbb R$. Let $\mathcal N\subseteq\mathcal D_n$ be nonempty, convex and open in $\mathcal D_n$, with every point of $\mathcal N$ having all coordinates positive, and suppose $R(D',D_{\rm tr})>r$ for every $D'\in\mathcal N$. Then there exist $G:\iota\to\mathbb R$ and $a\in\mathbb R$ with
--   $$\mathbb E_D[G]\le a<\mathbb E_{D'}[G]\qquad\text{for all } D\in\{D\in\mathcal D_n: R(D,D_{\rm tr})\le r\},\ D'\in\mathcal N,$$
--   where $\mathbb E_D[G]=\sum_i D_iG_i$.
--
--   This is the separation step of the proof of Proposition 1: the $R$-ball is convex because $R$ is convex in its first argument, it is disjoint from $\mathcal N$, and an open convex set can be strictly separated from a disjoint convex set.
--
--   **Formalization Note** The paper takes $\mathcal N$ convex "without loss of generality"; here convexity and nonemptiness are hypotheses. The hypothesis that $\mathcal N$ lies in the relative interior of the simplex is a disclosed restriction: in the proof $\mathcal N$ is a small neighbourhood of a point $\lambda D+(1-\lambda)D_{\rm tr}$, which has full support because $D_{\rm tr}$ does.
-- source:
--   Bertsimas and Van Parys, Bootstrap robust prescriptive analytics, arXiv:1711.09974v2, B.2 (proof of Proposition 1), p. 27, "By the Hahn–Banach separation Theorem …"

import Mathlib
import Definitions.Def_BootRobust_Optimality_Setting

namespace BootRobust.Optimality

/-- B.2, p. 27: the `R`-ball `{D ∈ 𝒟ₙ : R(D, D_tr) ≤ r}` and a convex, relatively open, nonempty set
`N` on which `R(·, D_tr) > r` are separated by a linear functional `D ↦ 𝔼_D[G] = ∑ i, D i * G i`:
`𝔼_D[G] ≤ a < 𝔼_{D'}[G]` for every `D` in the ball and every `D' ∈ N`. The set `N` lies in the
relative interior of the simplex (all coordinates positive). -/
theorem separation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : (ι → ℝ) → (ι → ℝ) → EReal) (hR : IsDistributionDistance R)
    (Dtr : ι → ℝ) (hDtr : Dtr ∈ stdSimplex ℝ ι) (r : ℝ)
    (N : Set (ι → ℝ)) (hN : relOpen N) (hNconv : Convex ℝ N) (hNne : N.Nonempty)
    (hNpos : ∀ D' ∈ N, ∀ i, 0 < D' i) (hRN : ∀ D' ∈ N, (r : EReal) < R D' Dtr) :
    ∃ G : ι → ℝ, ∃ a : ℝ,
      (∀ D ∈ stdSimplex ℝ ι, R D Dtr ≤ (r : EReal) → ∑ i, D i * G i ≤ a) ∧
      (∀ D' ∈ N, a < ∑ i, D' i * G i) := by sorry

end BootRobust.Optimality

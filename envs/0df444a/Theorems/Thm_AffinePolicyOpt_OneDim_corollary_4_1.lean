-- Prove2me | Theorems.Thm_AffinePolicyOpt_OneDim_corollary_4_1
-- name    : AffinePolicyOpt.OneDim.corollary_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T13:07:48.547077+00:00
-- url     : https://prove2.me/theorems/991d6fc0-db85-405d-a0e9-8b629668a3bc
-- title:
--   Corollary 4.1, p. 9 — max of θ₁ + f(θ₂) is the same over 𝒫, conv(𝒫), 𝒮, r-side(𝒫), z-hull(𝒮) and r-side(z-hull(𝒮))
-- statement:
--   Let $\mathcal S\subset\mathbb R^2$ be a finite nonempty set of points $(\theta_1,\theta_2)$, let $\mathcal P$ be a set with $\mathcal S\subseteq\mathcal P\subseteq\operatorname{conv}(\mathcal S)$ (for instance a possibly non-convex polygon with vertex set $\mathcal S$), and let $f:\mathbb R\to\mathbb R$ be convex. Let $y_0,\dots,y_m$ be the points of $\operatorname{r-side}(\mathcal S)$ listed by increasing $\theta_2$ (this is the counter-clockwise order from $y_0=y^-$ to $y_m=y^+$), and let $\operatorname{z-hull}(\mathcal S)=\{y_0+\sum_{i=1}^m w_i(y_i-y_{i-1}):0\le w_i\le1\}$. Then the maxima
--   $$\max_{\mathcal P},\quad \max_{\operatorname{conv}(\mathcal P)},\quad \max_{\mathcal S},\quad \max_{\operatorname{r-side}(\mathcal P)},\quad \max_{\operatorname{z-hull}(\mathcal S)},\quad \max_{\operatorname{r-side}(\operatorname{z-hull}(\mathcal S))}$$
--   of $\theta_1+f(\theta_2)$ are all attained and all equal.
--
--   The corollary lets the proof switch freely between feasible sets that share the same right side: it is how the paper shows that replacing the optimal control by an affine one, and the convex cost by an affine one, leaves the min-max value unchanged.
--
--   **Formalization Note** The right side is the set of extreme points of $\operatorname{conv}(\cdot)+\{(-t,0):t\ge0\}$; the page's alternative formula with the downward cone $\operatorname{cone}([0;-1])$ is a misprint. The page defines the vertices $y_i$ by counter-clockwise numbering; here the chain is given as data, with hypotheses that it enumerates $\operatorname{r-side}(\mathcal S)$ and that $\theta_2$ is strictly increasing along it, which determines it uniquely. The polygon $\mathcal P$ is generalised to any set between $\mathcal S$ and $\operatorname{conv}(\mathcal S)$.
-- source:
--   Bertsimas, Iancu & Parrilo, Optimality of Affine Policies in Multi-stage Robust Optimization, arXiv:0904.3986v1, p. 9, Corollary 4.1, with Definitions 4.1–4.2 (21)–(22), p. 8

import Mathlib
import Definitions.Def_AffinePolicyOpt_OneDim_Zonogon

namespace AffinePolicyOpt.OneDim

/-- Corollary 4.1: for a finite nonempty `S ⊆ ℝ²`, any set `P` with `S ⊆ P ⊆ conv(S)` (a polygon
with vertex set `S`), any convex `f`, and the right-side vertices `y_0, …, y_m` of `conv(S)`
listed in order of increasing `θ_2`, the maxima of `θ_1 + f(θ_2)` over `P`, `conv(P)`, `S`,
`r-side(P)`, `z-hull(S)` and `r-side(z-hull(S))` are all attained and equal. -/
theorem corollary_4_1 (S : Finset (ℝ × ℝ)) (hS : S.Nonempty) (P : Set (ℝ × ℝ))
    (hSP : (S : Set (ℝ × ℝ)) ⊆ P) (hPS : P ⊆ convexHull ℝ (S : Set (ℝ × ℝ)))
    (f : ℝ → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (m : ℕ) (y : Fin (m + 1) → ℝ × ℝ) (hy_mono : StrictMono (fun i => (y i).2))
    (hy_range : Set.range y = rside (S : Set (ℝ × ℝ))) :
    ∃ μ : ℝ,
      IsGreatest ((fun θ : ℝ × ℝ => θ.1 + f θ.2) '' P) μ ∧
      IsGreatest ((fun θ : ℝ × ℝ => θ.1 + f θ.2) '' convexHull ℝ P) μ ∧
      IsGreatest ((fun θ : ℝ × ℝ => θ.1 + f θ.2) '' (S : Set (ℝ × ℝ))) μ ∧
      IsGreatest ((fun θ : ℝ × ℝ => θ.1 + f θ.2) '' rside P) μ ∧
      IsGreatest ((fun θ : ℝ × ℝ => θ.1 + f θ.2) '' zhullChain y) μ ∧
      IsGreatest ((fun θ : ℝ × ℝ => θ.1 + f θ.2) '' rside (zhullChain y)) μ := by sorry

end AffinePolicyOpt.OneDim

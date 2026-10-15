-- Prove2me | Theorems.Thm_CompetitiveChores_RichFamily_corollary_25
-- name    : CompetitiveChores.RichFamily.corollary_25
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:00:42.569594+00:00
-- url     : https://prove2.me/theorems/b3a9c336-a14e-452c-a716-6e5e270e0ffe
-- title:
--   Corollary 25 — at most min{(2m−1)^{n(n−1)/2}, (2n−1)^{m(m−1)/2}} Pareto faces meeting ℝ^n_<0 and competitive utility profiles
-- statement:
--   Let $n,m\ge1$, let $v\in\mathbb R^{n\times m}_{<0}$ be a matrix of values and $b\in\mathbb R^n_{<0}$ a vector of budgets. Then the number of faces $f$ of the Pareto frontier with $f\cap\mathbb R^n_{<0}\neq\emptyset$ and the number of competitive utility profiles for the budgets $b$ are both at most
--   $$\min\Big\{(2m-1)^{\frac{n(n-1)}{2}},\ (2n-1)^{\frac{m(m-1)}{2}}\Big\}.$$
--
--   In particular both sets are finite, and for a fixed number of agents (or of chores) their size is polynomial in the number of chores (or agents). The competitive rule for chores is multi-valued, and this bound is what makes its complete enumeration feasible.
--
--   **Formalization Note** Faces of the Pareto frontier are the sets of maximizers of $\langle\tau,u\rangle$ over $\mathcal U(v)$ for $\tau\in\mathbb R^n_{>0}$, counted as sets (different $\tau$ exposing the same face count once). Both counts are cardinalities in $\mathbb N\cup\{\infty\}$; neither set is assumed finite. $n,m\ge1$ are added: the paper's sets of agents and chores are non-empty. The bound is computed in the natural numbers, where $n(n-1)/2$ and $m(m-1)/2$ are exact.
-- source:
--   Brânzei and Sandomirskiy, Algorithms for Competitive Division of Chores, arXiv:1907.01766v2, p. 27, §4.2, Corollary 25

import Mathlib
import Definitions.Def_CompetitiveChores_RichFamily_Setting
import Definitions.Def_CompetitiveChores_RichFamily_Graphs

namespace CompetitiveChores.RichFamily

variable {n m : ℕ}

/-- Corollary 25, p. 27: the number of faces `f` of the Pareto frontier with `f ∩ ℝ^n_{<0} ≠ ∅` and the
number of competitive utility profiles for the budgets `b` are both at most
`min{(2m − 1)^{n(n−1)/2}, (2n − 1)^{m(m−1)/2}}`. -/
theorem corollary_25 (hn : 0 < n) (hm : 0 < m) (v : Fin n → Fin m → ℝ) (hv : ∀ i j, v i j < 0)
    (b : Fin n → ℝ) (hb : ∀ i, b i < 0) :
    {f | f ∈ paretoFaces v ∧ ∃ u ∈ f, ∀ i, u i < 0}.encard ≤
        ((min ((2 * m - 1) ^ (n * (n - 1) / 2)) ((2 * n - 1) ^ (m * (m - 1) / 2)) : ℕ) : ℕ∞) ∧
      {u | IsCompetitiveProfile v b u}.encard ≤
        ((min ((2 * m - 1) ^ (n * (n - 1) / 2)) ((2 * n - 1) ^ (m * (m - 1) / 2)) : ℕ) : ℕ∞) := by sorry

end CompetitiveChores.RichFamily

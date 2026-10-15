-- Prove2me | Theorems.Thm_CompetitiveChores_RichFamily_lemma_23
-- name    : CompetitiveChores.RichFamily.lemma_23
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:00:44.516425+00:00
-- url     : https://prove2.me/theorems/431ec7bd-7b2d-4b3d-9640-16ff0751a0d7
-- title:
--   Lemma 23 (first bullet) — a rich family of at most min{(2m−1)^{n(n−1)/2}, (2n−1)^{m(m−1)/2}} graphs
-- statement:
--   Let $n,m\ge1$ and $v\in\mathbb R^{n\times m}_{<0}$. There is a rich family $\mathcal G(v)$ of bipartite graphs on $([n],[m])$ whose number of elements satisfies
--   $$|\mathcal G(v)|\le\min\Big\{(2m-1)^{\frac{n(n-1)}{2}},\ (2n-1)^{\frac{m(m-1)}{2}}\Big\}.$$
--
--   The bound is polynomial in $m$ for a fixed number of agents and polynomial in $n$ for a fixed number of chores; it is the size estimate behind the strongly polynomial enumeration of competitive utility profiles.
--
--   **Formalization Note** Only the first bullet of Lemma 23 is stated. The second bullet (enumerating the family takes time $O(m^{n(n-1)/2+1})$ for fixed $n$ and $O(n^{m(m-1)/2+1})$ for fixed $m$) is a running-time claim and is not formalized. The family is asserted to exist; it is not tied to the paper's Algorithm 2. The exponents $n(n-1)/2$ and $m(m-1)/2$ are exact natural numbers, and $2m-1$, $2n-1$ are natural numbers under $n,m\ge1$.
-- source:
--   Brânzei and Sandomirskiy, Algorithms for Competitive Division of Chores, arXiv:1907.01766v2, p. 24, §4.2, Lemma 23, first bullet

import Mathlib
import Definitions.Def_CompetitiveChores_RichFamily_Setting
import Definitions.Def_CompetitiveChores_RichFamily_Graphs

namespace CompetitiveChores.RichFamily

variable {n m : ℕ}

/-- Lemma 23, first bullet, p. 24: there is a rich family of bipartite graphs with at most
`min{(2m − 1)^{n(n−1)/2}, (2n − 1)^{m(m−1)/2}}` elements. -/
theorem lemma_23 (hn : 0 < n) (hm : 0 < m) (v : Fin n → Fin m → ℝ) (hv : ∀ i j, v i j < 0) :
    ∃ 𝒢 : Finset (Finset (Fin n × Fin m)), IsRich v (𝒢 : Set (Finset (Fin n × Fin m))) ∧
      𝒢.card ≤ min ((2 * m - 1) ^ (n * (n - 1) / 2)) ((2 * n - 1) ^ (m * (m - 1) / 2)) := by sorry

end CompetitiveChores.RichFamily

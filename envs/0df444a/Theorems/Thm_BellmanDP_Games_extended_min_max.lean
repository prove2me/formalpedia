-- Prove2me | Theorems.Thm_BellmanDP_Games_extended_min_max
-- name    : BellmanDP.Games.extended_min_max
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T20:56:18.991129+00:00
-- url     : https://prove2.me/theorems/5b76a022-4497-408d-a7e1-d7040bf85b26
-- title:
--   Chapter X, Theorem 7 — the extended min-max theorem for ratios of bilinear forms
-- statement:
--   Let $A=(a_{ij})$ and $B=(b_{ij})$ be real $M\times N$ matrices with $M,N\ge1$, and let $p$ and $q$ range over distribution vectors, that is, probability vectors on $\{1,\dots,M\}$ and $\{1,\dots,N\}$. If there is a constant $d>0$ with
--   $$\sum_{i,j}b_{ij}\,p_i\,q_j\ \ge\ d\qquad\text{for all distribution vectors }p\text{ and }q,$$
--   then
--   $$\max_p\ \min_q\ \frac{\sum_{i,j}a_{ij}\,p_i\,q_j}{\sum_{i,j}b_{ij}\,p_i\,q_j}\;=\;\min_q\ \max_p\ \frac{\sum_{i,j}a_{ij}\,p_i\,q_j}{\sum_{i,j}b_{ij}\,p_i\,q_j},$$
--   with both extrema attained.
--
--   The theorem extends von Neumann's min-max theorem from a bilinear payoff to a ratio of two bilinear forms. Bellman uses it as a criterion for non-zero-sum games and for the approximate solution of non-zero-sum games of survival (§§ 22 and 24).
--
--   **Formalization Note** The index sets are arbitrary nonempty finite types, and distribution vectors are points of the standard simplex. The conclusion is that some real $v$ is both the attained max-min and the attained min-max of the ratio. Because the denominator is at least $d>0$, no division by zero occurs.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter X, § 23, Theorem 7, p. 308

import Mathlib
import Definitions.Def_BellmanDP_Games_MinMax

namespace BellmanDP.Games

/-- Bellman, *Dynamic Programming*, Ch. X, Theorem 7, p. 308 (the extended min-max theorem).
If `Σ_{i,j} b_ij p_i q_j ≥ d > 0` for all distribution vectors `p` and `q`, then
`Max_p Min_q (Σ a_ij p_i q_j)/(Σ b_ij p_i q_j) = Min_q Max_p (Σ a_ij p_i q_j)/(Σ b_ij p_i q_j)`:
both extrema exist and are equal. Distribution vectors are the points of the standard simplices;
the index types are nonempty (`p = (p_1, …, p_M)` with `M ≥ 1`, `q = (q_1, …, q_N)` with
`N ≥ 1`, § 2). -/
theorem extended_min_max {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
    (A B : Matrix ι κ ℝ) (d : ℝ) (hd : 0 < d)
    (hB : ∀ p ∈ stdSimplex ℝ ι, ∀ q ∈ stdSimplex ℝ κ, d ≤ bilin B p q) :
    ∃ v : ℝ, IsMaxMinMinMaxValue (fun p q => bilin A p q / bilin B p q)
      (stdSimplex ℝ ι) (stdSimplex ℝ κ) v := by sorry

end BellmanDP.Games

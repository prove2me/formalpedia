-- Prove2me | Theorems.Thm_AdWordsMSVV_Tradeoff_lemma_4
-- name    : AdWordsMSVV.Tradeoff.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:31:13.350258+00:00
-- url     : https://prove2.me/theorems/01ef8060-4dbc-4c2f-940a-d76a5e071d73
-- title:
--   Lemma 4, p. 10 — y* is an optimal solution of D(π, ψ) for every instance and tradeoff function
-- statement:
--   Let $k\ge1$ and let $a=(a_1,\dots,a_{k-1})$ be any vector with $a_i\ge0$. Put $l=Aa$, i.e. $l_i=\sum_{j=1}^{i}(1+\frac{i-j}{k})a_j$, and let $D(\pi,\psi)$ be the LP
--   $$\min\ l\cdot y\quad\text{s.t.}\quad A^{\mathsf T}y\ge c,\ y\ge0,$$
--   which has the constraints of the dual $D$ of §4 and objective $l$. Then $y^*_i=\frac1k(1-\frac1k)^{k-i-1}$ is feasible for $D(\pi,\psi)$, and
--   $$l\cdot y^*\le l\cdot y\quad\text{for every feasible }y .$$
--
--   In the paper $a$ is the vector $(\alpha_1,\dots,\alpha_{k-1})$ of numbers of bidders of each type in the run of the algorithm on instance $\pi$ with tradeoff function $\psi$; the lemma says that the dual optimum does not depend on $\pi$ or $\psi$.
--
--   **Formalization Note** The instance and the tradeoff function enter $D(\pi,\psi)$ only through $a$, whose entries are counts and hence nonnegative. The statement therefore quantifies over every nonnegative $a$, which covers every instance and every monotonically decreasing $\psi$.
-- source:
--   Mehta, Saberi, Vazirani, Vazirani, AdWords and generalized on-line matching, J. ACM (2007), DOI 10.1145/1284320.1284321, p. 10, Lemma 4 (D(π, ψ) defined on pp. 9–10)

import Mathlib
import Definitions.Def_AdWordsMSVV_Tradeoff_LP

namespace AdWordsMSVV.Tradeoff
theorem lemma_4 (k : ℕ) (hk : 1 ≤ k) (a : ℕ → ℝ) (ha : ∀ i ∈ Finset.Icc 1 (k - 1), 0 ≤ a i) :
    DualFeasible k (yStar k) ∧
    ∀ y : ℕ → ℝ, DualFeasible k y →
      ∑ i ∈ Finset.Icc 1 (k - 1), lVec k a i * yStar k i ≤
        ∑ i ∈ Finset.Icc 1 (k - 1), lVec k a i * y i := by sorry
end AdWordsMSVV.Tradeoff

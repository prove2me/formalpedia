-- Prove2me | Theorems.Thm_Disjunctive_Dominants_constructive_alpha_p
-- name    : Disjunctive.Dominants.constructive_alpha_p
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T17:10:09.596274+00:00
-- url     : https://prove2.me/theorems/d672f24c-93c9-4da1-b2f4-40f61f2f8612
-- title:
--   Theorem 13.5 — the constructive characterization of α_P
-- statement:
--   This is Theorem 13.5 of Balas's *Disjunctive Programming*: a constructive recipe for the
--   upper-separation value $\alpha_P$, reducing it to finding a single distinguished coordinate of
--   $x^*$.
--
--   Let $P=\{x\in[0,1]^n:ax\ge1\}$ be upper monotone, $S(\alpha):=\{j\in N:x^*_j\le\alpha\}$, and
--   $g(\alpha):=\sum_{j\in S(\alpha)}a_jx^*_j/(1-a(N\setminus S(\alpha)))$. Let $x^*_q$ be the
--   **greatest** coordinate value $x^*_j$ satisfying both $a(N\setminus S(x^*_j))<1$ and
--   $x^*_j\le g(x^*_j)$. Then
--   $$
--   S(\alpha_P) = S(x^*_q), \qquad \alpha_P = \sum_{j\in S(x^*_q)} \frac{a_jx^*_j}{1-a(N\setminus
--   S(x^*_q))} = g(x^*_q).
--   $$
--
--   The book's proof rests on Lemma 13.4's seven equivalent conditions for $\alpha_P\ge\alpha$
--   (not drafted this pass): at $\alpha=\alpha_P$ several of these become tight equalities, from
--   which $S(\alpha_P)$ is shown to equal $S(x^*_j)$ for the specific $j$ maximizing $x^*_j$
--   subject to the two side conditions.
--
--   **Formalization Note.** `xq`'s defining property is hypothesized via `IsGreatest` over the
--   explicit candidate set $\{x^*_j : a(N\setminus S(x^*_j))<1,\ x^*_j\le g(x^*_j)\}$, matching
--   Theorem 1.1's own convention for a book-asserted extremal value (`01-intro-duality`), rather
--   than assuming existence and uniqueness as unstated background facts.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 219, Theorem 13.5

import Mathlib
import Definitions.Def_Disjunctive_Dominants_Basic

namespace Disjunctive.Dominants

/-- Theorem 13.5 (Balas §13.1, p. 219): for `P = {x∈[0,1]ⁿ : ax≥1}` upper monotone and `x* ∈
ℝⁿ_+`, let `x*_q` be the greatest coordinate value `x*_j` such that `a(N\S(x*_j))<1` and `x*_j ≤
g(x*_j)`. Then `S(α_P) = S(x*_q)` and `α_P = Σ_{j∈S(x*_q)} a_jx*_j / (1-a(N\S(x*_q)))`. The page takes `x* ≥ 0`; at `x* = -1` the infimum defining `α_P` is over an unbounded-below
set and reads `0`. -/
theorem constructive_alpha_p {n : ℕ} (a xstar : Fin n → ℝ) (ha : 0 ≤ a) (hxstar : 0 ≤ xstar)
    (P : Set (Fin n → ℝ)) (hP : P = UnitCube n ∩ {x | 1 ≤ dotProduct a x})
    (hupper : IsUpperMonotone P) (xq : ℝ)
    (hxq : IsGreatest {v : ℝ | ∃ j, v = xstar j ∧
      SumOver a (Finset.univ \ SAlpha xstar (xstar j)) < 1 ∧ xstar j ≤ GAlpha a xstar (xstar j)}
      xq) :
    SAlpha xstar (AlphaP P xstar) = SAlpha xstar xq ∧ AlphaP P xstar = GAlpha a xstar xq := by sorry

end Disjunctive.Dominants

-- Prove2me | Theorems.Thm_ConstATSP_Gap_integrality_gap_le_319
-- name    : ConstATSP.Gap.integrality_gap_le_319
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:45:42.213492+00:00
-- url     : https://prove2.me/theorems/4e32e741-3161-441f-92df-e1b96ac259da
-- title:
--   Theorem 11.1, p. 61 — the integrality gap of the asymmetric Held–Karp relaxation is at most 319
-- statement:
--   Let $G=(V,E)$ be a strongly connected digraph with at least two vertices (parallel edges allowed) and $w:E\to\mathbb R_{\ge0}$ a nonnegative weight function. Then for every feasible solution $x$ of the asymmetric Held–Karp relaxation LP$(G,w)$ there is a tour $F$ of $G$ (a connected Eulerian edge multiset visiting every vertex, i.e. a closed walk visiting every vertex at least once) with
--   $$\sum_{e\in E}F(e)\,w(e)\ \le\ 319\sum_{e\in E}w(e)\,x(e).$$
--   Equivalently, the integrality gap of the asymmetric Held–Karp relaxation, the maximum ratio between the optimum of ATSP and the Held–Karp lower bound, is at most $319$.
--
--   The paper's Theorem 1.1 gives a polynomial-time algorithm returning a tour of weight at most $506$ times the Held–Karp lower bound, the first constant-factor approximation for ATSP; §11 observes that without the polynomial-time requirement the constants improve and the gap is at most $319$.
--
--   **Formalization Note** "Integer optimum $\le 319\cdot$ LP optimum" is stated for every feasible $x$; this is equivalent because the LP minimum is attained, and it avoids defining the LP value as an infimum. Tours are edge multisets $F:E\to\mathbb N$ (Def. 2.1). The hypothesis $|V|\ge2$ is added: for a single vertex without a loop no tour exists, while LP$(G,w)$ is feasible with value $0$.
-- source:
--   Svensson, Tarnawski, Végh, A constant-factor approximation algorithm for the asymmetric traveling salesman problem, J. ACM 67(6) (2020), accepted manuscript (LSE Research Online 106582), p. 61, Theorem 11.1 (with footnote 1, p. 3, and §11, Integrality gap, p. 61)

import Mathlib
import Definitions.Def_ConstATSP_Gap_Graph

namespace ConstATSP.Gap

theorem integrality_gap_le_319 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    (G : Graph V E) (w : E → ℝ) (hV : 2 ≤ Fintype.card V) (hG : IsStronglyConnected G)
    (hw : ∀ e, 0 ≤ w e) (x : E → ℝ) (hx : IsHeldKarpFeasible G x) :
    ∃ F : E → ℕ, IsTour G F ∧ ∑ e, (F e : ℝ) * w e ≤ 319 * ∑ e, w e * x e := by sorry

end ConstATSP.Gap

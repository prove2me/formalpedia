-- Prove2me | Theorems.Thm_ConstATSP_Gap_lemma_2_2
-- name    : ConstATSP.Gap.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:44:45.674052+00:00
-- url     : https://prove2.me/theorems/616a1772-0d8f-4241-8366-6cf45d966dc6
-- title:
--   Lemma 2.2, p. 8 — DUAL(G, w) has an optimal solution with laminar support
-- statement:
--   Let $G=(V,E)$ be a strongly connected digraph and $w:E\to\mathbb R_{\ge0}$ a nonnegative weight function. Then DUAL$(G,w)$,
--   $$\max\sum_{\emptyset\ne S\subsetneq V}2y_S\quad\text{s.t.}\quad\sum_{S:\,e\in\delta(S)}y_S+\alpha_u-\alpha_v\le w(e)\ \ (e=(u,v)\in E),\qquad y\ge0,$$
--   has an optimal solution $(\alpha,y)$ whose support $\{S: y_S>0\}$ is a laminar family of vertex sets.
--
--   The laminar optimal dual is what makes the reduction of Theorem 2.4 to laminarly-weighted instances possible.
--
--   **Formalization Note** Only the first sentence of Lemma 2.2 is formalized; the polynomial-time computation of such a solution is not. Optimality is stated as: the solution is dual feasible and no dual feasible solution has larger objective. The hypotheses (strong connectivity, $w\ge0$) are the paper's standing assumptions on ATSP inputs (Def. 1.2); without them the dual may be unbounded and have no optimum. One vertex is allowed here (the dual then has no $y$-variables).
-- source:
--   Svensson, Tarnawski, Végh, A constant-factor approximation algorithm for the asymmetric traveling salesman problem, J. ACM 67(6) (2020), accepted manuscript (LSE Research Online 106582), p. 8, Lemma 2.2 (first sentence)

import Mathlib
import Definitions.Def_ConstATSP_Gap_Graph

namespace ConstATSP.Gap

theorem lemma_2_2 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    (G : Graph V E) (w : E → ℝ) (hG : IsStronglyConnected G) (hw : ∀ e, 0 ≤ w e) :
    ∃ (a : V → ℝ) (y : Finset V → ℝ), IsDualFeasible G w a y ∧
      (∀ (a' : V → ℝ) (y' : Finset V → ℝ), IsDualFeasible G w a' y' → dualObj y' ≤ dualObj y) ∧
      IsLaminar ((properSets V).filter (fun S => 0 < y S)) := by sorry

end ConstATSP.Gap

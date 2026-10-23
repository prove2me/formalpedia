-- Prove2me | Theorems.Thm_BayesGroupHard_VertexCover_eq_17
-- name    : BayesGroupHard.VertexCover.eq_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:18:26.575116+00:00
-- url     : https://prove2.me/theorems/a3206f69-1b42-4b9d-bad1-34254b94728e
-- title:
--   (17), p. 30 — a set of at most $0.85n$ vertices has $\mathbb P_1\{\Sigma = \Sigma^\star\} \ge \bar q(0.85)^n > 0.42^n$
-- statement:
--   Let $n \ge 1$ and let $\Sigma^\star \subseteq \{1,\dots,n\}$ have $|\Sigma^\star| \le 0.85n$. With $\bar p = 0.4$ and $\bar q(\alpha) = \bar p^\alpha(1-\bar p)^{1-\alpha}$,
--   $$\mathbb P_1\{\Sigma = \Sigma^\star\} = \bar p^{|\Sigma^\star|}(1-\bar p)^{n - |\Sigma^\star|} \ge \bar q(0.85)^n > 0.42^n.$$
--
--   In the YES case $\Sigma^\star$ is a small vertex cover, whose likelihood dominates that of all large covers.
--
--   **Formalization Note.** The bound uses only $|\Sigma^\star| \le 0.85n$, so it is stated for every such set; the paper applies it to a vertex cover. $\bar q(0.85)$ uses real powers; the paper's $(0.425\ldots)^n$ is a truncated decimal and is not stated. The hypothesis $n \ge 1$ is added: at $n = 0$ the strict inequality would read $1 < 1$.
-- source:
--   Hązła, Jadbabaie, Mossel & Rahimian, Bayesian Decision Making in Groups is Hard, arXiv:1705.04770v4, p. 30, (17)

import Mathlib
import Definitions.Def_BayesGroupHard_VertexCover_Model

open Finset

namespace BayesGroupHard.VertexCover

/-- (17), p. 30: a set `Σ⋆` of at most `0.85 n` vertices has
`P_1{Σ = Σ⋆} ≥ q̄(0.85)^n > 0.42^n`, for `n ≥ 1`. -/
theorem eq_17 (n : ℕ) (hn : 1 ≤ n) (C : Finset (Fin n)) (hC : (C.card : ℝ) ≤ 85 / 100 * n) :
    qbar (85 / 100) ^ n ≤ (4 / 10 : ℝ) ^ C.card * (6 / 10 : ℝ) ^ (n - C.card) ∧
      (42 / 100 : ℝ) ^ n < qbar (85 / 100) ^ n := by sorry

end BayesGroupHard.VertexCover

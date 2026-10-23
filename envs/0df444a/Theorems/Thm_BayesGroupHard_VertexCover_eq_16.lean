-- Prove2me | Theorems.Thm_BayesGroupHard_VertexCover_eq_16
-- name    : BayesGroupHard.VertexCover.eq_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:18:24.139248+00:00
-- url     : https://prove2.me/theorems/36ca03e9-b511-40a4-b3d9-c84109726ced
-- title:
--   (16), p. 30 — $\mathbb P_1\{|\Sigma| > 0.998n\} \le e^{-nD_{KL}(0.998\|0.4)} < 0.41^n$
-- statement:
--   Let $\Sigma$ be a random subset of $\{1,\dots,n\}$ containing each element independently with probability $\bar p = 0.4$ (the law of the vertex signals under $\theta = 1$). For $n \ge 1$,
--   $$\mathbb P_1\{|\Sigma| > 0.998n\} \le \exp\bigl(-n D_{KL}(0.998\|0.4)\bigr) < 0.41^n.$$
--
--   It bounds the total $\theta = 1$ likelihood of large vertex covers in the YES case.
--
--   **Formalization Note.** The probability is the finite sum of $0.4^{|C|}0.6^{n-|C|}$ over subsets $C$ with $|C| > 0.998n$. The paper's intermediate value $(0.4061\ldots)^n$ is a truncated decimal and is not stated. The hypothesis $n \ge 1$ is added: at $n = 0$ the strict inequality would read $1 < 1$.
-- source:
--   Hązła, Jadbabaie, Mossel & Rahimian, Bayesian Decision Making in Groups is Hard, arXiv:1705.04770v4, p. 30, (16)

import Mathlib
import Definitions.Def_bernoulliRelativeEntropy
import Definitions.Def_BayesGroupHard_VertexCover_Model

open Finset

namespace BayesGroupHard.VertexCover

/-- (16), p. 30: `P_1{|Σ| > 0.998 n} ≤ exp(-n D_KL(0.998 ‖ 0.4)) < 0.41^n`, for `n ≥ 1`. -/
theorem eq_16 (n : ℕ) (hn : 1 ≤ n) :
    ∑ C ∈ univ.filter (fun C : Finset (Fin n) => 998 / 1000 * (n : ℝ) < C.card),
          (4 / 10 : ℝ) ^ C.card * (6 / 10 : ℝ) ^ (n - C.card) ≤
        Real.exp (-((n : ℝ) * BanditAlgorithm.bernoulliRelativeEntropy (998 / 1000) (4 / 10))) ∧
      Real.exp (-((n : ℝ) * BanditAlgorithm.bernoulliRelativeEntropy (998 / 1000) (4 / 10))) <
        (41 / 100 : ℝ) ^ n := by sorry

end BayesGroupHard.VertexCover

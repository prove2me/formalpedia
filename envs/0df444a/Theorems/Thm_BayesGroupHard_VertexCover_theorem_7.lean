-- Prove2me | Theorems.Thm_BayesGroupHard_VertexCover_theorem_7
-- name    : BayesGroupHard.VertexCover.theorem_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:18:40.302679+00:00
-- url     : https://prove2.me/theorems/4994ab5b-5343-4745-9766-14f4cc6a2e9e
-- title:
--   Theorem 7, pp. 29–30 — Chernoff bound $\Pr\{\sum_k s_k \ge \alpha n\} \le e^{-n D_{KL}(\alpha\|p)}$ for i.i.d. Bernoulli sums
-- statement:
--   Let $s_1, \dots, s_n \in \{0,1\}$ be i.i.d. with $\mathbb P\{s_k = 1\} = p$, and let $0 \le p \le \alpha \le 1$. Then
--   $$\Pr\Bigl\{\sum_{k=1}^n s_k \ge \alpha n\Bigr\} \le \exp\bigl(-n D_{KL}(\alpha \| p)\bigr), \qquad D_{KL}(\alpha\|p) = \alpha\log\frac\alpha p + (1-\alpha)\log\frac{1-\alpha}{1-p}. \tag{14, 15}$$
--
--   This is the tail bound with which the paper controls the weight of large vertex covers in the YES case.
--
--   **Formalization Note.** The probability is written as a finite sum: the outcome is identified with the set $C = \{k : s_k = 1\} \subseteq \{1,\dots,n\}$, of probability $p^{|C|}(1-p)^{n-|C|}$, and the event is $|C| \ge \alpha n$ (a real inequality). $D_{KL}$ is the published `BanditAlgorithm.bernoulliRelativeEntropy α p`, which is (15) with Lean's conventions $x/0 = 0$, $\log 0 = 0$; at the endpoints $p = 0$, $\alpha = 1$ these give the correct bound, so no further hypothesis is needed.
-- source:
--   Hązła, Jadbabaie, Mossel & Rahimian, Bayesian Decision Making in Groups is Hard, arXiv:1705.04770v4, pp. 29–30, Theorem 7, (14), (15)

import Mathlib
import Definitions.Def_bernoulliRelativeEntropy
import Definitions.Def_BayesGroupHard_VertexCover_Model

open Finset

namespace BayesGroupHard.VertexCover

/-- Theorem 7, pp. 29–30: for i.i.d. Bernoulli(`p`) signals `s_1, …, s_n` and `p ≤ α ≤ 1`,
`Pr{Σ_k s_k ≥ α n} ≤ exp(-n D_KL(α ‖ p))`. The event is written as the set of subsets
`C = {k : s_k = 1}` of `Fin n`, each of probability `p^|C| (1-p)^(n-|C|)`. -/
theorem theorem_7 (n : ℕ) (p α : ℝ) (hp : 0 ≤ p) (hpα : p ≤ α) (hα : α ≤ 1) :
    ∑ C ∈ univ.filter (fun C : Finset (Fin n) => α * (n : ℝ) ≤ C.card),
        p ^ C.card * (1 - p) ^ (n - C.card) ≤
      Real.exp (-((n : ℝ) * BanditAlgorithm.bernoulliRelativeEntropy α p)) := by sorry

end BayesGroupHard.VertexCover

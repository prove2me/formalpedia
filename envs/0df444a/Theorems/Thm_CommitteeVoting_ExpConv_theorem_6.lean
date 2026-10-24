-- Prove2me | Theorems.Thm_CommitteeVoting_ExpConv_theorem_6
-- name    : CommitteeVoting.ExpConv.theorem_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:41:41.042481+00:00
-- url     : https://prove2.me/theorems/9550a4b3-e776-47ae-8cc9-5940496f7e29
-- title:
--   Theorem 6, p. 50 — Chernoff–Hoeffding for a Poisson binomial: Pr[X > np̄ + t] ≤ e^{−2t²/n} and Pr[X < np̄ − t] ≤ e^{−2t²/n}
-- statement:
--   Let $X_1,\dots,X_n$ ($n\ge 1$) be independent Bernoulli random variables with $\Pr[X_i=1]=p_i$, and let $X=\sum_{i=1}^n X_i$, a Poisson binomial random variable with parameters $p_1,\dots,p_n$. Put $\bar p=\frac1n\sum_{i=1}^n p_i$. Then for every $t>0$
--   $$\Pr\bigl[X>n\bar p+t\bigr]\le e^{-2t^2/n}\qquad\text{and}\qquad\Pr\bigl[X<n\bar p-t\bigr]\le e^{-2t^2/n}.$$
--
--   These are the two one-sided Chernoff–Hoeffding bounds (Dubhashi and Panconesi 2009, Theorem 1.1) that the proof of Theorem 3 applies to the vote counts of an honest and of a dishonest producer.
--
--   **Formalization Note** The paper states Theorem 6 without conditions on $t$ and $n$; it is false for negative $t$ (all $p_i=1$, $t=-n$ gives probability $1>e^{-2n}$) and divides by $n$, so $t>0$ and $n\ge1$ are added, as in the source it cites and as the proof of Theorem 3 uses it ("for all $t>0$"). The product $n\bar p$ is written as $\sum_i p_i$. Each $X_i$ is real-valued, measurable, and takes the values $0$ or $1$ almost surely; the independence is mutual independence of $X_1,\dots,X_n$.
-- source:
--   Benhaim, Falk, Tsoukalas, Scaling Blockchains: Can Committee-based Consensus Help?, arXiv:2110.08673v2, p. 50, Theorem 6, eqs. (87)–(88); Poisson binomial per Definition 7, p. 49

import Mathlib

open MeasureTheory ProbabilityTheory

namespace CommitteeVoting.ExpConv
theorem theorem_6 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 1 ≤ n) (X : Fin n → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (hind : iIndepFun X P) (h01 : ∀ i, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1)
    (q : Fin n → ℝ) (hq : ∀ i, P.real {ω | X i ω = 1} = q i) {t : ℝ} (ht : 0 < t) :
    P.real {ω | ∑ i, q i + t < ∑ i, X i ω} ≤ Real.exp (-(2 * t ^ 2 / n)) ∧
      P.real {ω | ∑ i, X i ω < ∑ i, q i - t} ≤ Real.exp (-(2 * t ^ 2 / n)) := by sorry
end CommitteeVoting.ExpConv

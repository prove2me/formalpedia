-- Prove2me | Theorems.Thm_BauerleRiederMDP_AmericanPut_theorem_11_2_1
-- name    : BauerleRiederMDP.AmericanPut.theorem_11_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:31:40.649601+00:00
-- url     : https://prove2.me/theorems/fe4a84bc-1bb3-40f6-8fa4-99cc1f3ce629
-- title:
--   Theorem 11.2.1 — credit granting: $J_n$ increasing in $x$ and $n$, threshold cancellation sets (corrected: $x<x^*_n$ or $x\le x^*_n$)
-- statement:
--   Consider the credit granting model on $E=\mathbb R$ with transition kernel $Q^X$, measurable reward $c$ and discount factor $\beta\in(0,1]$, and suppose that an upper bounding function exists, that
--   1. $x\mapsto c(x)$ is increasing, and
--   2. $Q^X$ is stochastically monotone.
--
--   Let $J_0\equiv0$, $J_n(x)=\max\{0,c(x)+\beta\int J_{n-1}(y)Q^X(dy\mid x)\}$. Then for every horizon $N$:
--
--   - **(a)** $J_n(x)$ is increasing in $x$ and in $n$.
--   - **(b)** There exist thresholds $x^*_N\le\dots\le x^*_1$ in $[-\infty,\infty]$ and sets $S^*_n$, each equal to $\{x\in E\mid x<x^*_n\}$ or to $\{x\in E\mid x\le x^*_n\}$, such that $S^*_n$ is the set of states in which the credit is cancelled by an optimal policy: with $f^*_n:=1_{S^*_n}$, each $f^*_n$ is a maximizer of $J_{n-1}$,
--   $$\mathbf 1_{\{x\notin S^*_n\}}\Big(c(x)+\beta\int J_{n-1}\,dQ^X(\cdot\mid x)\Big)=J_n(x),\qquad 1\le n\le N,$$
--   and the credit policy $(f^*_N,\dots,f^*_1)$ attains $J_N$.
--
--   The theorem says that a bank should cancel the credit exactly when the borrower's information falls below a level, and that this level rises as the remaining duration shrinks.
--
--   **Formalization Note** Thresholds are extended reals (the book's $\inf\emptyset=\infty$). The value of the policy is `policyValue`, defined by reward iteration.
--
--   Differences from the source:
--   - correction: b) S*_n = {x ∈ E | x < x*_n} and f*_n = 1_{S*_n} is optimal → S*_n = {x < x*_n} or S*_n = {x ≤ x*_n}, with f*_n = 1_{S*_n} optimal; reason: with Q^X(·|x) = δ_x, c = −1 on (−∞, 0] and c = 1 on (0, ∞), β = 1, b ≡ 1, N = 1, cancelling is strictly optimal at 0 and extending strictly optimal at every x > 0, so no set {x < x*} works
--   - reading: 'the optimal credit policy (f*_N, …, f*_1)' → each f*_n is a maximizer of J_{n−1} and policyValue S N = J_N; reason: optimality in the sense of Theorems 2.3.8 and 10.1.5: maximizers at every stage, and the policy attains the value
--   - encoding: value of a policy as an expectation over the information process → policyValue defined by reward iteration; reason: the book's Theorem 2.3.4 (J_{nπ} = T_{f_n} J_{n−1,π})
--   - encoding: Q^X stochastically monotone (Definition B.3.13) → Q^X(·|x) ≤_st Q^X(·|x') for x ≤ x' (distribution functions); reason: equivalent by the remark after Definition B.3.13 and Theorem B.3.3
--   - encoding: 'c(x) is arbitrary', Q^X a transition kernel → c measurable, Q^X a Markov kernel; reason: one-stage rewards and kernels of a Markov Decision Model are measurable (§10.1, p.304)
--   - encoding: thresholds x*_n := inf{…} with inf ∅ = ∞ → thresholds in EReal; reason: the infimum can be +∞ (empty set) or −∞ (unbounded below); only the order is used, no arithmetic
-- source:
--   N. Bäuerle and U. Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, Theorem 11.2.1, pp.340–341, PDF 348–349

import Mathlib
import Definitions.Def_BauerleRiederMDP_AmericanPut_CreditModel_IsUpperBoundingFunction
import Definitions.Def_BauerleRiederMDP_AmericanPut_IsStochasticallyMonotone
import Definitions.Def_BauerleRiederMDP_AmericanPut_CreditModel_J
import Definitions.Def_BauerleRiederMDP_AmericanPut_CreditModel_policyValue

open MeasureTheory ProbabilityTheory

namespace BauerleRiederMDP.AmericanPut

open Classical in
/-- **Theorem 11.2.1** (Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011),
pp.340–341, PDF 348–349), corrected: for the credit granting model with an upper bounding function, `c`
increasing and `Q^X` stochastically monotone,
a) `J_n(x)` is increasing in `x` and `n`;
b) there exist thresholds `x*_N ≤ … ≤ x*_1` such that the set `S*_n` of states in which the credit is
cancelled is `{x ∈ E | x < x*_n}` **or** `{x ∈ E | x ≤ x*_n}`, and the credit policy `(f*_N, …, f*_1)`,
`f*_n := 1_{S*_n}`, is optimal: each `f*_n` is a maximizer of `J_{n−1}` and the policy attains `J_N`.

**Formalization Note.** The book prints only the strict form `S*_n = {x < x*_n}`, which is false: with `Q^X(·|x)
= δ_x`, `c = −1` on `(−∞, 0]` and `c = 1` on `(0, ∞)`, `β = 1`, `b ≡ 1` and `N = 1`, cancelling is strictly
optimal at `x = 0` and extending strictly optimal at every `x > 0`, so no set `{x < x*}` is the cancellation set
of an optimal policy. Thresholds are in `[−∞, ∞]` (`EReal`, the book's `inf ∅ = ∞`). -/
theorem theorem_11_2_1 (M : CreditModel) (hb : ∃ b : ℝ → ℝ, M.IsUpperBoundingFunction b)
    (hc : Monotone M.c) (hQ : IsStochasticallyMonotone M.QX) (N : ℕ) :
    -- a)
    ((∀ n : ℕ, Monotone (M.J n)) ∧ ∀ m n : ℕ, m ≤ n → ∀ x : ℝ, M.J m x ≤ M.J n x) ∧
    -- b) (corrected: strict or non-strict threshold)
    ∃ (xstar : ℕ → EReal) (S : ℕ → Set ℝ),
      (∀ m n : ℕ, 1 ≤ m → m ≤ n → n ≤ N → xstar n ≤ xstar m) ∧
      (∀ n : ℕ, 1 ≤ n → n ≤ N →
        S n = {x : ℝ | (x : EReal) < xstar n} ∨ S n = {x : ℝ | (x : EReal) ≤ xstar n}) ∧
      (∀ n : ℕ, 1 ≤ n → n ≤ N → ∀ x : ℝ,
        (if x ∈ S n then 0 else M.c x + M.beta * ∫ y, M.J (n - 1) y ∂(M.QX x)) = M.J n x) ∧
      ∀ x : ℝ, M.policyValue S N x = M.J N x := by sorry

end BauerleRiederMDP.AmericanPut

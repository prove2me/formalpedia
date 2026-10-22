-- Prove2me | Theorems.Thm_DynamicOnlineLP_LowerBound_lemma11
-- name    : DynamicOnlineLP.LowerBound.lemma11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T20:20:00.938786+00:00
-- url     : https://prove2.me/theorems/8868b423-c46a-4e87-b7ca-f5256bf9e957
-- title:
--   Lemma 11 — given a constant-probability prefix of fair coins, the total of 2k coins exceeds and falls short of k by ⌈√k/2⌉ with constant probability
-- statement:
--   Let $k\ge 2$ and $0\le r\le k$, and let $Y_1,\dots,Y_{2k}$ be independent random variables, each equal to $0$ or $1$ with probability $1/2$. Put $S=\sum_{j=1}^{2k}Y_j$ (so $\mathbb E S=k$) and $d=\lceil\sqrt k/2\rceil$. Then there is an absolute constant $c$ with $0<c<1$, independent of $k$ and $r$, such that with probability at least $c$ the first $r$ variables $Y_1,\dots,Y_r$ take values $y$ for which both conditional probabilities are at least $c$:
--
--   $$\Pr\bigl(S\ge k+d\mid Y_{1..r}=y\bigr)\ge c\quad\text{and}\quad \Pr\bigl(S\le k-d\mid Y_{1..r}=y\bigr)\ge c .$$
--
--   In particular $\Pr\bigl(|S-k|\ge\lceil\sqrt k/2\rceil\mid Y_1,\dots,Y_r\bigr)\ge c$ on that event. This is an anti-concentration statement for a binomial sum conditioned on a partially revealed prefix; in the proof of Theorem 2 it says that when an online algorithm must decide on a profit-2 input of pair $i$, the profit values of that pair seen so far leave both "too many" and "too few" profit-3 inputs possible with constant probability.
--
--   **Formalization Note** All probabilities are finite uniform averages: the prefix $y$ ranges over $\{0,1\}^r$ and the remaining variables $u$ over $\{0,1\}^{2k-r}$, with $S=\#\{j:y_j=1\}+\#\{j:u_j=1\}$; the conditional probability given $y$ is the fraction of $u$ in the event. The deviation is $\lceil\sqrt k/2\rceil$ as in the displayed formula; since $S$ is an integer, "$S-k\ge\sqrt k/2$" (the sentence's form) is equivalent. The page states the lemma for $k\ge 1$; the two-sided form asserted in its sentence ("can be greater or less than its expected value $k$ by $\sqrt k/2$ with equal constant probability") fails at $k=r=1$ (given $Y_1=1$ the sum cannot be $\le 0$; given $Y_1=0$ it cannot be $\ge 2$), so it is stated for $k\ge 2$. "Equal constant probability" is formalized as "each at least $c$".
-- source:
--   Agrawal, Wang, Ye, A Dynamic Near-Optimal Algorithm for Online Linear Programming, Oper. Res. 62(4), 2014, p. 889, Lemma 11

import Mathlib

namespace DynamicOnlineLP.LowerBound

/-- Agrawal–Wang–Ye 2014, Lemma 11 (p. 889), two-sided form, for `k ≥ 2`. Let `Y_1, …, Y_{2k}` be
independent fair `0/1` coins and `r ≤ k`; write `y ∈ {0,1}^r` for the values of `Y_1, …, Y_r` and
`u ∈ {0,1}^{2k-r}` for those of `Y_{r+1}, …, Y_{2k}`, so that `∑_j Y_j = #y + #u` (numbers of ones),
and let `d = ⌈√k / 2⌉`. There is an absolute constant `0 < c < 1` such that, with probability at
least `c` over `y`, both conditional probabilities given `Y_1, …, Y_r = y`,
`P(∑_j Y_j ≥ k + d | y)` and `P(∑_j Y_j ≤ k - d | y)`, are at least `c`. All probabilities are
uniform averages over `{0,1}^r` and `{0,1}^{2k-r}`. (The page states it for `k ≥ 1`; at `k = 1`,
`r = 1` no prefix admits both deviations, so the two-sided form needs `k ≥ 2`.) -/
theorem lemma11 :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧ ∀ k r : ℕ, 2 ≤ k → r ≤ k →
      c ≤ ((Finset.univ.filter (fun y : Fin r → Bool =>
            c ≤ ((Finset.univ.filter (fun u : Fin (2 * k - r) → Bool =>
                    k + ⌈Real.sqrt (k : ℝ) / 2⌉₊ ≤
                      (Finset.univ.filter (fun j => y j = true)).card +
                        (Finset.univ.filter (fun j => u j = true)).card)).card : ℝ) /
                  2 ^ (2 * k - r) ∧
            c ≤ ((Finset.univ.filter (fun u : Fin (2 * k - r) → Bool =>
                    (Finset.univ.filter (fun j => y j = true)).card +
                        (Finset.univ.filter (fun j => u j = true)).card +
                      ⌈Real.sqrt (k : ℝ) / 2⌉₊ ≤ k)).card : ℝ) /
                  2 ^ (2 * k - r))).card : ℝ) / 2 ^ r := by sorry

end DynamicOnlineLP.LowerBound

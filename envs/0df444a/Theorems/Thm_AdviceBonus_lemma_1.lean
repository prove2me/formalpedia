-- Prove2me | Theorems.Thm_AdviceBonus_lemma_1
-- name    : AdviceBonus.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:45:50.596277+00:00
-- url     : https://prove2.me/theorems/6e61ed94-b6b6-414f-a008-99a289a74112
-- title:
--   Lemma 1 — the advisor's optimal recommendation is the cutoff rule $(\bar q_1,\bar q^A_2,\bar q^B_2)$ (corrected: a clamped cutoff's own endpoint is excluded from the opposite interval)
-- statement:
--   Let the posterior distribution satisfy the standing assumptions, let $w>0$, and fix any compensation profile $(f_A,b_A,f_B,b_B)$. When customers follow the recommendation, the cutoff rule is optimal for the advisor's sequential problem:
--
--   1. After a first sale of $m_1\in\{A,B\}$, for every $q_2\in[0,1]$: if $q_2\ge\bar q^{m_1}_2$ and $\bar q^{m_1}_2<1$, recommending $A$ to the second customer is optimal; if $q_2\le\bar q^{m_1}_2$ and $\bar q^{m_1}_2>0$, recommending $B$ is optimal.
--   2. For every $q_1\in[0,1]$: if $q_1\ge\bar q_1$ and $\bar q_1<1$, recommending $A$ to the first customer (followed by optimal advice to the second) is optimal; if $q_1\le\bar q_1$ and $\bar q_1>0$, recommending $B$ is optimal.
--
--   So the recommendation pattern is $(m_1,m_2)=(A,A)$ for $q_1\in[\bar q_1,1]$, $q_2\in[\bar q^A_2,1]$; $(A,B)$ for $q_1\in[\bar q_1,1]$, $q_2\in[0,\bar q^A_2]$; $(B,A)$ for $q_1\in[0,\bar q_1]$, $q_2\in[\bar q^B_2,1]$; and $(B,B)$ for $q_1\in[0,\bar q_1]$, $q_2\in[0,\bar q^B_2]$, where an interval is dropped at an endpoint where its cutoff is clamped to the other end of $[0,1]$. At an interior cutoff both recommendations are optimal.
--
--   The lemma justifies using the cutoffs (2)–(4) in the sales probabilities and profits.
--
--   Differences from the source:
--   - correction: (A, A) if q2 ∈ [q̄A2, 1], (A, B) if q2 ∈ [0, q̄A2], etc. (closed intervals, also for q1) → the same closed intervals, except the endpoint q2 = q̄ when q̄ is clamped to the other end: A optimal for q2 ∈ [q̄, 1] when q̄ < 1, B optimal for q2 ∈ [0, q̄] when q̄ > 0 (likewise for q1); reason: at a clamped cutoff the closed interval is false at that endpoint: f_A = 2w, b_A = f_B = b_B = 0 gives q̄A2 = 0 (footnote 19), and at q2 = 0 recommending B pays w < 2w
--   - reading: q̄1 by (4), no corner convention → clamped to [0, 1]; reason: the convention of footnote 19 for (2) and (3)
--   - reading: density g > 0 on [0, 1], hazard rate increasing on [0, 1] → g continuous and positive on [0, 1], hazard rate weakly increasing on [0, 1); reason: the proofs use continuity (intermediate value theorem, p.35) and the hazard rate is undefined at q = 1
--   - encoding: advisor payoffs include w_l; continuation payoff Z^{m1} → w_l dropped; the first recommendation is evaluated with the optimal expected second-stage payoff; reason: w_l shifts both compared payoffs equally; Z^A, Z^B are the optimal continuation under the cutoff rule
-- source:
--   Honda–Inderst–Ottaviani, When Liability is Not Enough, SSRN 4125013 (May 2022), Lemma 1, p.11

import Mathlib
import Definitions.Def_AdviceBonus_Model
import Definitions.Def_AdviceBonus_Advisor

namespace AdviceBonus

/-- **Lemma 1**, p.11 (Honda–Inderst–Ottaviani, SSRN 4125013, May 2022). When customers follow the
recommendation, the advisor's optimal recommendation is the cutoff rule: after the first sale `m₁`,
recommending A to the second customer is optimal if `q₂ ∈ [q̄^{m₁}_2, 1]` and recommending B is
optimal if `q₂ ∈ [0, q̄^{m₁}_2]`; to the first customer (followed by optimal advice to the second),
recommending A is optimal if `q₁ ∈ [q̄_1, 1]` and recommending B if `q₁ ∈ [0, q̄_1]`. At an interior
cutoff both recommendations are optimal (the advisor is indifferent).

**Formalization Note** The paper's closed intervals fail at one endpoint of a clamped cutoff: with
`f_A = 2w`, `b_A = f_B = b_B = 0` footnote 19 gives `q̄^A_2 = 0`, and at `q₂ = 0` recommending B
(the paper's `(A, B)` for `q₂ ∈ [0, q̄^A_2]`) pays `w < 2w`. The statement keeps every closed
interval except that endpoint: `[q̄, 1]` for A only when `q̄ < 1`, `[0, q̄]` for B only when
`q̄ > 0`. -/
theorem lemma_1 (D : Dist) (w : ℝ) (hw : 0 < w) (sA sB : ℝ × ℝ) :
    (∀ m₁ : Firm, ∀ q₂ ∈ Set.Icc (0 : ℝ) 1,
      (cutoff2 w sA sB m₁ ≤ q₂ → cutoff2 w sA sB m₁ < 1 →
        ∀ m : Firm, secondPayoff w sA sB m₁ q₂ m ≤ secondPayoff w sA sB m₁ q₂ .A) ∧
      (q₂ ≤ cutoff2 w sA sB m₁ → 0 < cutoff2 w sA sB m₁ →
        ∀ m : Firm, secondPayoff w sA sB m₁ q₂ m ≤ secondPayoff w sA sB m₁ q₂ .B)) ∧
    (∀ q₁' ∈ Set.Icc (0 : ℝ) 1,
      (q1 D w sA sB ≤ q₁' → q1 D w sA sB < 1 →
        ∀ m : Firm, firstPayoff D w sA sB q₁' m ≤ firstPayoff D w sA sB q₁' .A) ∧
      (q₁' ≤ q1 D w sA sB → 0 < q1 D w sA sB →
        ∀ m : Firm, firstPayoff D w sA sB q₁' m ≤ firstPayoff D w sA sB q₁' .B)) := by sorry

end AdviceBonus

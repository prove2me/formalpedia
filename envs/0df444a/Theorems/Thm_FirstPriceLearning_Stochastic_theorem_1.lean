-- Prove2me | Theorems.Thm_FirstPriceLearning_Stochastic_theorem_1
-- name    : FirstPriceLearning.Stochastic.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T06:28:43.118272+00:00
-- url     : https://prove2.me/theorems/4ba98647-68b5-42a5-82c0-a8556011fb01
-- title:
--   Theorem 1, p. 10 — with iid private values some bidding policy has 𝔼[R_T] ≤ C√T log^2.5 T
-- statement:
--   **Bidding with stochastic private values.** In $T$ repeated first-price auctions with censored feedback (only the winning bid $\max\{b_t,m_t\}$ is revealed), let the private values $v_1,\dots,v_T$ be iid from an unknown distribution $F$ on $[0,1]$ and the highest other bids $m_1,\dots,m_T$ iid from an unknown CDF $G$ on $[0,1]$. There is an absolute constant $C>0$ such that for every $T\ge2$ there exists a bidding policy $\pi$ with
--
--   $$
--   \mathbb E[R_T(\pi;v)]\ \le\ C\sqrt T\,\log^{2.5}T
--   $$
--
--   for **every** pair $(F,G)$, where $R_T$ is the regret (3) against the oracle that knows $G$, and the expectation is joint over $v$, the HOBs and the policy's randomness. The constant does not depend on $T$, $F$ or $G$; the policy may depend on $T$ but not on $F$ or $G$.
--
--   This is the first $\tilde O(\sqrt T)$ regret guarantee for learning to bid in first-price auctions against an arbitrary unknown HOB distribution; the policy is Algorithm 3 on the quantized auction (Corollary 1).
--
--   **Formalization Note.** A policy is non-anticipating by construction: its round-$t$ bid sees only its internal randomness, $v_1,\dots,v_t$ and the feedback $\max\{b_s,m_s\}$ of rounds $s<t$. The statement starts at $T\ge2$ because at $T=1$ the right side is $0$ while the regret of an uninformed first bid can be positive. $\log^{2.5}T$ is $(\log T)^{5/2}$ with the natural logarithm. The conclusion also asserts that the regret is integrable, so the expectation is genuine.
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, p. 10, Theorem 1

import Mathlib
import Definitions.Def_FirstPriceLearning_Stochastic_Policy

namespace FirstPriceLearning.Stochastic

open MeasureTheory

/-- Theorem 1 (p. 10), bidding with stochastic private values: there is an absolute constant
`C > 0` such that for every horizon `T ≥ 2` some non-anticipating randomized bidding policy `π`
with censored feedback (built from `T` only) satisfies, for every value law `F` and every HOB law
`G` on `[0, 1]`, with `v_1, …, v_T` iid `F` and `m_1, …, m_T` iid `G`,
`𝔼[R_T(π; v)] ≤ C √T (log T)^{5/2}`, the expectation being joint over `v`, `m` and the policy's
randomness (the regret is integrable, so the expectation is a genuine one). -/
theorem theorem_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℕ, 2 ≤ T → ∃ π : Policy T,
      ∀ (F μG : Measure ℝ) [IsProbabilityMeasure F] [IsProbabilityMeasure μG],
        F (Set.Icc (0 : ℝ) 1)ᶜ = 0 → μG (Set.Icc (0 : ℝ) 1)ᶜ = 0 →
        Integrable (π.regretOf μG) (π.jointLaw F μG) ∧
          π.expectedRegret F μG ≤ C * Real.sqrt T * Real.log T ^ ((5 : ℝ) / 2) := by sorry

end FirstPriceLearning.Stochastic

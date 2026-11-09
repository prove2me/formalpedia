-- Prove2me | Theorems.Thm_FairShareAlmostAll_Slack_faithful_rounding
-- name    : FairShareAlmostAll.Slack.faithful_rounding
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:53:00.800902+00:00
-- url     : https://prove2.me/theorems/72b441a6-6f5c-41a8-a86b-38eaa7b5d463
-- title:
--   Lemma 1.2 — Faithful rounding
-- statement:
--   For arbitrary finite agent and good sets $J,U$, let $y$ be a nonnegative fractional allocation and $u_i$ nonnegative additive values. Suppose $m_i\ge0$ bounds $u_i(g)$ wherever $y_{ig}>0$. There is a finite randomized partial allocation $B$ with exact marginals and, in every positive-probability outcome,
--   $$\Pr(g\in B_i)=y_{ig},\qquad B_i\subseteq\{g:y_{ig}>0\},\qquad u_i(B_i)\ge\sum_{g\in U}y_{ig}u_i(g)-m_i.$$
--   All clauses hold simultaneously, and both finite sets may be empty. This provides the arbitrary-input rounding interface required for configuration tails and reserve allocations.
--
--   Differences from the source:
--   - encoding: distribution with finite support over integral allocations → real weights on the finite type of bundle families, with disjointness on positive-probability outcomes; reason: all bundle families form a finite carrier; zero weights discard invalid or unused outcomes
--   - encoding: arbitrary finite agent and good sets J and U → finite types with Fintype and DecidableEq instances; reason: classical decidable equality and finite enumeration exist for every finite set, including empty sets; these instances exclude no source case
-- source:
--   Tomer Ezra, Tamar Garbuz, Fair Share Allocations for Almost All Agents, STOC 2027 submission #480 (October 2026), printed p. 7 (PDF p. 8), Lemma 1.2; source.pdf SHA256 c9f47a54f6a9e1568951e8e3845ff79c34d51d391a68fd697d37d8ba29cc7491

import Mathlib
import Definitions.Def_AnyPriceShare_Bidding_Basic
import Definitions.Def_FairShareAlmostAll_Slack_FiniteAllocation

namespace FairShareAlmostAll.Slack

theorem faithful_rounding {J U : Type} [Fintype J] [Fintype U] [DecidableEq J] [DecidableEq U]
    (u : J → U → ℝ) (hu : ∀ i g, 0 ≤ u i g)
    (y : J → U → ℝ) (hy : FractionalAllocation y)
    (loss : J → ℝ) (hloss : ∀ i, 0 ≤ loss i)
    (hbound : ∀ i g, 0 < y i g → u i g ≤ loss i) :
    ∃ D : FiniteLaw (J → Finset U),
      (∀ i g, probability D (fun A => g ∈ A i) = y i g) ∧
      ∀ A, 0 < D.weight A → PartialAllocation A ∧
        ∀ i, (∀ g ∈ A i, 0 < y i g) ∧
          (∑ g, y i g * u i g) - loss i ≤ ∑ g ∈ A i, u i g := by sorry

end FairShareAlmostAll.Slack

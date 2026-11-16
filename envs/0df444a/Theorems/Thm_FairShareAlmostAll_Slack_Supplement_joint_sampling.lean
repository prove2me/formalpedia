-- Prove2me | Theorems.Thm_FairShareAlmostAll_Slack_Supplement_joint_sampling
-- name    : FairShareAlmostAll.Slack.Supplement.joint_sampling
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:10:21.049878+00:00
-- url     : https://prove2.me/theorems/eb9271a3-4460-4fff-8277-718db6cca23b
-- title:
--   Lemma 4.1 — Joint sampling with bounded error
-- statement:
--   Let $I$ be a finite nonempty set of agents. For each $i\in I$ let $\mathcal P_i$ be a finite nonempty set of choices and $Q_i$ a probability distribution on $\mathcal P_i$. Fix a positive integer $s$, a real $\xi\ge0$, and real functions $f_{r,i}:\mathcal P_i\to\mathbb R$ ($i\in I$, $1\le r\le s$), possibly negative, with
--
--   $$\sum_{r=1}^{s}|f_{r,i}(P)|\le\xi\qquad(i\in I,\ P\in\mathcal P_i).$$
--
--   Then there is a joint distribution of choices $(P_i)_{i\in I}$ with exact marginals $\Pr(P_i=P)=Q_i(P)$ for all $i$ and $P$, such that in every outcome
--
--   $$\Bigl|\sum_{i\in I}f_{r,i}(P_i)-\sum_{i\in I}\mathbb E_{P\sim Q_i}[f_{r,i}(P)]\Bigr|\le2\xi\qquad(1\le r\le s).$$
--
--   The choices may be dependent. The lemma is a discrepancy-type rounding statement: it selects one configuration per agent while keeping several aggregate request sums within an additive error of their means, deterministically rather than with high probability. Proposition 4.1 uses it to select configurations.
--
--   Differences from the source:
--   - encoding: distributions with finite support and index set $\{1,\dots,s\}$ → the live mission's `FiniteLaw` on the finite product type and indices `Fin s`; reason: same finite distributions; "in every outcome" is read as every tuple of positive weight
-- source:
--   Tomer Ezra, Tamar Garbuz, Fair Share Allocations for Almost All Agents, STOC 2027 submission #480 (October 2026), printed p. 13 (PDF p. 14), §4.1 setup and Lemma 4.1; proof printed pp. 13–15 (PDF pp. 14–16); source.pdf SHA256 c9f47a54f6a9e1568951e8e3845ff79c34d51d391a68fd697d37d8ba29cc7491

import Mathlib
import Definitions.Def_FairShareAlmostAll_Slack_FiniteAllocation

namespace FairShareAlmostAll.Slack.Supplement

open FairShareAlmostAll.Slack AnyPriceShare.Bidding

theorem joint_sampling {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (C : I → Type) [∀ i, Fintype (C i)] [∀ i, Nonempty (C i)]
    (Q : ∀ i, FiniteLaw (C i)) (s : ℕ) (hs : 0 < s) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (f : Fin s → ∀ i, C i → ℝ) (hf : ∀ i (P : C i), ∑ r, |f r i P| ≤ ξ) :
    ∃ D : FiniteLaw (∀ i, C i),
      (∀ i (P : C i), probability D (fun x => x i = P) = (Q i).weight P) ∧
      ∀ x, 0 < D.weight x → ∀ r,
        |∑ i, f r i (x i) - ∑ i, expectation (Q i) (f r i)| ≤ 2 * ξ := by sorry

end FairShareAlmostAll.Slack.Supplement

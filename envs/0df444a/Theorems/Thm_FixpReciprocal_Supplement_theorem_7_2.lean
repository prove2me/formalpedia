-- Prove2me | Theorems.Thm_FixpReciprocal_Supplement_theorem_7_2
-- name    : FixpReciprocal.Supplement.theorem_7_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:51:49.436126+00:00
-- url     : https://prove2.me/theorems/2b8bce14-2e64-42e4-83c2-85436419235f
-- title:
--   Theorem 7.2 — exact second-price throttling equilibria are FIXP-complete, and FIXP-hard with at most three distinct positive bids per item
-- statement:
--   An instance has $n$ bidders, $m$ items, nonnegative rational bids $b=(b_{\ell,s})$ and positive rational budgets $M=(M_\ell)$. Bidder $\ell$ participates in all $m$ auctions with probability $\alpha_\ell\in[0,1]$, independently of the other bidders; each item is sold once in a second-price auction among the participants, a sole participant pays zero, and ties are resolved by a fixed priority order. Writing $\ell\succ_s\ell'$ when $\ell$ precedes $\ell'$ in decreasing bid order on item $s$ (with the priority), the **conditional payment** is
--   $$C_\ell(\alpha_{-\ell})=\sum_{s=1}^m\ \sum_{\ell':\,\ell\succ_s\ell'} b_{\ell',s}\,\alpha_{\ell'}\prod_{\ell''\ne\ell,\ \ell''\succ_s\ell'}(1-\alpha_{\ell''}),$$
--   and $P_\ell(\alpha)=\alpha_\ell C_\ell(\alpha_{-\ell})$. A vector $\alpha\in[0,1]^n$ is an **exact second-price throttling equilibrium** (Definition 7.1) if for every $\ell$: $P_\ell(\alpha)\le M_\ell$, and $P_\ell(\alpha)<M_\ell\implies\alpha_\ell=1$.
--
--   **Theorem.**
--
--   1. Given binary-encoded rational bids $b\in\mathbb Q_{\ge0}^{n\times m}$ and budgets $M\in\mathbb Q_{>0}^n$, finding an exact second-price throttling equilibrium $\alpha\in[0,1]^n$ is FIXP-complete.
--   2. The problem remains FIXP-hard when each item has at most three positive bids and these bids are pairwise distinct.
--
--   Under the second restriction ties between positive bids never occur, so the hardness does not depend on the tie-breaking rule for positive bids.
--
--   **Formalization Note** The problem is the published `throttlingProblemOn`, with the priority fixed to bidder index order (`IndexPriority`); the sparse class is `ThreeDistinctBids`.
--
--   Differences from the source:
--   - reading: ties are resolved by a fixed priority order → IndexPriority: prio = [0, 1, …, n−1], a lower bidder index has higher priority, the same order on every item; reason: the input of Theorem 7.2 is only (b, M), so the priority is not instance data; any fixed order is the index order after relabelling the bidders
--   - encoding: input (b, M) only → ThrottleData also encodes n, m and the priority list, which IndexPriority forces to equal List.range n; reason: the published encoding carries these fields; they are determined by the bids and add no instances
--   - encoding: conditional payment C_ℓ(α_{−ℓ}) of (32) and P_ℓ(α) = α_ℓ C_ℓ(α_{−ℓ}) → condPayment: the expectation, over independent participation of the other bidders, of ℓ's second-price payments when ℓ participates (ℓ pays the highest other participating bid, 0 if alone, on each item it wins under bid order with index priority); reason: summing over the highest-ranked other participant ℓ' below ℓ gives exactly the terms b_{ℓ',s} α_{ℓ'} ∏_{ℓ''≠ℓ, ℓ''≻_s ℓ'} (1 − α_{ℓ''}) of (32)
--   - encoding: hardness holds even when each item has at most three positive bids and these bids are pairwise distinct → second conjunct FIXPHard (throttlingProblemOn (IndexPriority ∧ ThreeDistinctBids)); reason: 'hardness holds' for the restricted problem is FIXP-hardness of the problem on that instance class
--   - encoding: bidders ℓ ∈ [n], items s ∈ [m] → Fin nb, Fin ng (0-based); WellFormed: nb rows of ng nonnegative rational bids, nb positive rational budgets; reason: Lean indexing; the same instances
-- source:
--   Shimizu, FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions (STOC 2027 submission, sha256 ffcad4a7…), Theorem 7.2, p.31 (PDF p.33); §7.1 and Definition 7.1, p.30 (PDF p.32), (32)–(34)

import Mathlib
import Definitions.Def_FixpReciprocal_FIXPComplete
import Definitions.Def_ExactAutobid_Equilibria_Throttling
import Definitions.Def_FixpReciprocal_Supplement_Classes

namespace FixpReciprocal.Supplement

open ExactAutobid.Equilibria

/-- **Theorem 7.2 (Second-price throttling).** Given binary-encoded rational bids `b ∈ ℚ_{≥0}^{n×m}`
and budgets `M ∈ ℚ_{>0}^n`, the problem of finding an exact second-price throttling equilibrium
`α ∈ [0, 1]^n` is FIXP-complete. Hardness holds even when each item has at most three positive bids
and these bids are pairwise distinct.

Shimizu, *FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions*, STOC 2027
submission (sha256 ffcad4a7…), Theorem 7.2, p.31; §7.1 and Definition 7.1, p.30, (32)–(34).

**Formalization Note.** The problem is the published `throttlingProblemOn`, whose `condPayment` is
the conditional payment `C_ℓ(α_{−ℓ})` of (32) and whose `IsThrottlingEq` is `α ∈ [0, 1]^n` with
(33)–(34). The fixed tie-breaking priority is the bidder index order (`IndexPriority`). The second
conjunct is FIXP-hardness of the problem restricted to `ThreeDistinctBids`. -/
theorem theorem_7_2 :
    FIXPComplete (throttlingProblemOn IndexPriority) ∧
      FIXPHard (throttlingProblemOn (fun d => IndexPriority d ∧ ThreeDistinctBids d)) := by sorry

end FixpReciprocal.Supplement

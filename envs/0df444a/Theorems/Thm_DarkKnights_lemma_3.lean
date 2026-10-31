-- Prove2me | Theorems.Thm_DarkKnights_lemma_3
-- name    : DarkKnights.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:42:36.689498+00:00
-- url     : https://prove2.me/theorems/064e52a9-4e2f-4e4b-ad22-cfc87f2cd7bb
-- title:
--   Lemma 3 — for $h>1/2$ the dealer injects to $b_n=a$ exactly on $b-hb\le a<hb$
-- statement:
--   Let $1/2<h\le1$, $b\ge0$ and $a\ge0$. Let
--   $$
--   b_n=\begin{cases} b & \text{if } a<b-hb,\\ a & \text{if } b-hb\le a<hb,\\ b & \text{if } a\ge hb,\end{cases}
--   $$
--   and let $\theta$ be the stake of Lemma 2 at this $b_n$. Then the offer $(b_n,\theta)$ lies in $[0,b]\times[0,1]$ and maximizes the dealer's ex-post payoff over all feasible offers, and it is followed by
--
--   1. liquidation if $a<b-hb$;
--   2. repayment if $b-hb\le a<hb$;
--   3. renegotiation if $a\ge hb$ and $hb<b$ (repayment, with identical payoffs, if $hb=b$).
--
--   The dealer injects exactly enough equity to avoid liquidation in the intermediate states; this is what drives the value of debt in Lemma 4.
--
--   **Formalization Note** The action after the offer is the tie-broken default decision with the face value in force.
--
--   Differences from the source:
--   - reading: the new amount of debt is $b_n$ → the offer $(b_n,\theta_{\text{Lemma 2}}(b_n))$ is dealer-optimal (not necessarily the unique optimum); reason: at $a=b-hb$ the dealer is indifferent between injecting and not (Appendix D); the stake is the one of Lemma 2, which Appendix D substitutes
--   - reading: $a\ge hb$: followed by renegotiation → renegotiation when $hb<b$, repayment when $hb=b$; reason: at $h=1$ renegotiation pays $b_r=hb=b=b_n$, the same as repayment, and the tie-break picks repayment
--   - reading: a given hedge ratio that satisfies $h>1/2$ → $1/2<h\le1$; reason: §2's standing conjecture $h\le1$ (p.15); for $h>1$ the printed $b_n=a$ exceeds $b$ when $b<a<hb$, and Appendix A gives $b_n=b$ there
-- source:
--   Danis, Gamba, Dark Knights: The Rise in Firm Intervention by CDS Investors, Authors' Accepted Manuscript (WRAP 172628, January 20, 2023) of Management Science, doi:10.1287/mnsc.2023.4717, §2, Lemma 3, p.17 (PDF 19); proof Appendix D, pp.43–44 (PDF 45–46); Figure 5, p.45 (PDF 47)

import Mathlib
import Definitions.Def_DarkKnights_Primitives
import Definitions.Def_DarkKnights_ActiveSellerModel

namespace DarkKnights

/-- **Lemma 3** (the dealer's optimal new face value of debt, `h > 1/2`).
Danis, Gamba, *Dark Knights*, Authors' Accepted Manuscript (WRAP 172628, January 20, 2023),
doi:10.1287/mnsc.2023.4717, §2, Lemma 3, p.17 (PDF p.19); proof Appendix D, pp.43–44
(PDF pp.45–46), Figure 5, p.45 (PDF p.47).

For `1/2 < h ≤ 1` (`h ≤ 1` is the §2 standing conjecture, p.15), `b ≥ 0`, `a ≥ 0`: let
`b_n = b` if `a < b − h b`, `b_n = a` if `b − h b ≤ a < h b`, `b_n = b` if `a ≥ h b`, and `θ` the
stake of Lemma 2 at this `b_n`. The offer `(b_n, θ)` is feasible and maximizes the dealer's
ex-post payoff over all feasible offers `[0, b] × [0, 1]`, and it is followed by liquidation if
`a < b − h b`, by repayment if `b − h b ≤ a < h b`, and, if `a ≥ h b`, by renegotiation when
`h b < b` (repayment when `h b = b`, i.e. `h = 1` or `b = 0`, with the same payoffs).

**Formalization Note** "The new amount of debt is b_n" is read as optimality of the offer, not
uniqueness: at `a = b − h b` the dealer is indifferent between injecting and not. The action
after acceptance is the tie-broken `defaultAction` with the face value in force. -/
theorem lemma_3 (a b h : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hh : 1 / 2 < h) (hh1 : h ≤ 1) :
    let bn : ℝ := if a < b - h * b then b else if a < h * b then a else b
    let θ : ℝ :=
      if bn ≤ h * b then (if h * b ≤ a then 1 - (a - h * b) / (a - bn) else 1)
      else (if h * b ≤ a then 0 else 1)
    (bn, θ) ∈ offerSet b ∧
      (∀ o ∈ offerSet b, dealerPayoff a b h o ≤ dealerPayoff a b h (bn, θ)) ∧
      (a < b - h * b →
        defaultAction a (faceValue a b h (bn, θ)) (h * b) = Action.liquidate) ∧
      (b - h * b ≤ a → a < h * b →
        defaultAction a (faceValue a b h (bn, θ)) (h * b) = Action.repay) ∧
      (h * b ≤ a → h * b < b →
        defaultAction a (faceValue a b h (bn, θ)) (h * b) = Action.renegotiate) ∧
      (h * b ≤ a → h * b = b →
        defaultAction a (faceValue a b h (bn, θ)) (h * b) = Action.repay) := by sorry

end DarkKnights

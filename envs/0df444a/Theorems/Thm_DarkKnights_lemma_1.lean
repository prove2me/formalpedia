-- Prove2me | Theorems.Thm_DarkKnights_lemma_1
-- name    : DarkKnights.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:41:50.622664+00:00
-- url     : https://prove2.me/theorems/bfb0257c-761a-430d-b437-e36ecf786eaa
-- title:
--   Lemma 1 — default decision: liquidate below $\min$ threshold, else repay ($b_n\le hb$) or renegotiate ($b_n>hb$)
-- statement:
--   Let $a\ge0$ be the asset value, $b\ge0$ the original face value of debt, $0\le b_n\le b$ the face value in force, and $h\ge0$ the lender's hedge ratio. The equity holders' optimal default decision is:
--
--   1. if $b_n\le hb$: liquidate if $a<b_n$, and repay the debt if $a\ge b_n$;
--   2. if $b_n>hb$: liquidate if $a<hb$, and renegotiate if $a\ge hb$.
--
--   This is the first step of the backward induction of §2: it determines in which states the dealer's intervention avoids liquidation.
--
--   **Formalization Note** The optimal decision is the equity-maximizing action with ties broken repay, renegotiate, liquidate, as the paper does on p.15.
--
--   Differences from the source:
--   - generalization: §2 standing conjecture $h\le1$ (p.15) → any $h\ge0$; reason: the proof (Appendix B) uses only eq. (12) and the two preference comparisons; the statement specializes to $0\le h\le1$
--   - encoding: the optimal decision → the tie-broken equity-maximizing action `defaultAction`; reason: the paper's own tie-breaks (p.15); Lemma 1's weak inequalities
-- source:
--   Danis, Gamba, Dark Knights: The Rise in Firm Intervention by CDS Investors, Authors' Accepted Manuscript (WRAP 172628, January 20, 2023) of Management Science, doi:10.1287/mnsc.2023.4717, §2, Lemma 1, p.16 (PDF 18); proof Appendix B, p.42 (PDF 44)

import Mathlib
import Definitions.Def_DarkKnights_Primitives

namespace DarkKnights

/-- **Lemma 1** (the equity holders' default decision in the active-CDS-seller model).
Danis, Gamba, *Dark Knights*, Authors' Accepted Manuscript (WRAP 172628, January 20, 2023),
doi:10.1287/mnsc.2023.4717, §2, Lemma 1, p.16 (PDF p.18); proof Appendix B, p.42 (PDF p.44).

With face value `b_n` in force and CDS protection `h b`: if `b_n ≤ h b`, the equity holders
liquidate if `a < b_n` and repay if `a ≥ b_n`; if `b_n > h b`, they liquidate if `a < h b` and
renegotiate if `a ≥ h b`.

**Formalization Note** The "optimal decision" is `defaultAction`, the equity-maximizing action
with ties broken repay ≻ renegotiate ≻ liquidate (p.15). The §2 standing conjecture `h ≤ 1`
(p.15) is not assumed: the lemma holds for every `h ≥ 0`. -/
theorem lemma_1 (a b bn h : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hbn : 0 ≤ bn) (hbnb : bn ≤ b)
    (hh : 0 ≤ h) :
    (bn ≤ h * b →
      (a < bn → defaultAction a bn (h * b) = Action.liquidate) ∧
      (bn ≤ a → defaultAction a bn (h * b) = Action.repay)) ∧
    (h * b < bn →
      (a < h * b → defaultAction a bn (h * b) = Action.liquidate) ∧
      (h * b ≤ a → defaultAction a bn (h * b) = Action.renegotiate)) := by sorry

end DarkKnights

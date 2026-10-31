-- Prove2me | Theorems.Thm_DarkKnights_comparison_7_15
-- name    : DarkKnights.comparison_7_15
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:42:52.366016+00:00
-- url     : https://prove2.me/theorems/5651ab63-d502-47e0-abe2-c615d8de2200
-- title:
--   Proof of Proposition 1(a) — for fixed $(k,b)$ and $h=1$ the intervening dealer weakly raises firm value (corrected: strict iff $k,b>0$)
-- statement:
--   Let $\alpha\in(0,1)$, $Z>0$, $\tau\in[0,1)$, $k,b\ge0$, and let $\sigma$ be any dealer-optimal strategy at $h=1$. Then the firm value of the active-CDS-buyer model at $h=1$ is at most the firm value of the model with an intervening dealer at $h=1$,
--   $$
--   V_1(k,b,1)\le V_2(k,b,1),
--   $$
--   and the inequality is strict exactly when $k>0$ and $b>0$.
--
--   This is the comparison of (7) and (15) on which the paper's proof of Proposition 1(a) rests.
--
--   Differences from the source:
--   - correction: for any capital $k$ and debt $b$, firm value is higher with a single protection seller → $\le$ always, $<$ iff $k>0$ and $b>0$; reason: at $b=0$ both (7) and (15) equal $-k+(1-\tau)Zk^\alpha/2$ (no debt, no liquidation), and at $k=0$ both values are $0$
--   - generalization: the value under the dealer's strategy of Lemmas 2–3 (Appendices A, D for other hedge ratios) → the value under every dealer-optimal strategy $\sigma$; reason: the paper's strategy is dealer-optimal, so this specializes to it; all optimal offers give every player the same payoff except at the indifference point $a=b-hb$, a null set of states (at $h\ge1$, $a\ge b$ the dealer is indifferent among offers with identical payoffs)
--   - reading: the CDS spread makes the protection seller break even including the equity injection (p.18) → premium $=-\mathbb E[\text{dealer's ex-post payoff}]$; reason: zero NPV for the protection seller (p.8); equals Lemma 4's bracket on the equilibrium path
-- source:
--   Danis, Gamba, Dark Knights: The Rise in Firm Intervention by CDS Investors, Authors' Accepted Manuscript (WRAP 172628, January 20, 2023) of Management Science, doi:10.1287/mnsc.2023.4717, §2, proof of Proposition 1, p.22 (PDF 24)

import Mathlib
import Definitions.Def_DarkKnights_Primitives
import Definitions.Def_DarkKnights_ActiveBuyerModel
import Definitions.Def_DarkKnights_ActiveSellerModel

namespace DarkKnights

/-- **Proof of Proposition 1(a): comparison of eqs. (7) and (15)**.
Danis, Gamba, *Dark Knights*, Authors' Accepted Manuscript (WRAP 172628, January 20, 2023),
doi:10.1287/mnsc.2023.4717, §2, proof of Proposition 1, p.22 (PDF p.24): "These two equations
show that for any capital k and debt b, firm value is higher with a single protection seller."

For `k, b ≥ 0` and every dealer-optimal strategy `σ` at `h = 1`, the firm value of model 1 at
`h = 1` is at most the firm value of model 2 at `h = 1`, and strictly smaller exactly when
`k > 0` and `b > 0`.

**Formalization Note** At `b = 0` (no debt) or `k = 0` (no assets) the two values coincide, so
"higher" holds strictly only for `k, b > 0`. -/
theorem comparison_7_15 (α Z τ k b : ℝ) (hα : 0 < α) (hα1 : α < 1) (hZ : 0 < Z) (hτ0 : 0 ≤ τ)
    (hτ1 : τ < 1) (hk : 0 ≤ k) (hb : 0 ≤ b) (σ : ℝ → ℝ × ℝ)
    (hσ : IsDealerOptimal α Z k b 1 σ) :
    firmValue1 α Z τ k b 1 ≤ firmValue2 α Z τ k b 1 σ ∧
      (firmValue1 α Z τ k b 1 < firmValue2 α Z τ k b 1 σ ↔ 0 < k ∧ 0 < b) := by sorry

end DarkKnights

-- Prove2me | Theorems.Thm_DiscServLine_SPT_proposition_5_iii_top
-- name    : DiscServLine.SPT.proposition_5_iii_top
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:18:31.720196+00:00
-- url     : https://prove2.me/theorems/2e825dc4-fe04-43a2-b00c-b2555e334ded
-- title:
--   Proposition 5 (iii), top end, p. 18 (PDF 18) — the optimal SPT price is concave on [t̲, t̄] and decreasing at t̄
-- statement:
--   Assume $0<c<\bar\theta$, $b>0$ and $\Lambda>0$, with $\Delta=0$ and non-preemptive SPT. Then problem (9) has an optimal service line, and for every optimal line $(\underline t,\bar t,\mu)$ the price schedule $P(t)=\bar\theta t-bt^2-c(t+W(t))$ of eq. (2)
--
--   1. is concave on the service line $[\underline t,\bar t]$, and
--   2. is decreasing at the top end: its derivative at $\bar t$ within $[\underline t,\bar t]$ exists and
--   $$\frac{d}{dt}P(\bar t)<0 .$$
--
--   The longest services are priced below slightly shorter ones, compensating their customers for the long SPT wait.
--
--   **Formalization Note** The derivative at $\bar t$ is the one-sided (left) derivative within $[\underline t,\bar t]$: the price is quoted only on the service line, and beyond $\bar t$ the waiting time is constant, so $P$ has a kink at $\bar t$. Existence of an optimum is stated explicitly.
-- source:
--   Debo & Li, Design and Pricing of Discretionary Service Lines, SSRN working paper 3054741 (Oct. 17, 2017), p. 18 (PDF 18), Proposition 5 (iii), first clause; proof p. 43 (PDF 43), (iii), (iii-a)

import Mathlib
import Definitions.Def_DiscServLine_SPT_Model

namespace DiscServLine.SPT

theorem proposition_5_iii_top (P : Params) (hP : P.Standing) :
    (∃ d, IsOptimal P d) ∧
      ∀ d, IsOptimal P d →
        ConcaveOn ℝ (Set.Icc d.lo d.hi) (price P d) ∧
        ∃ p < 0, HasDerivWithinAt (price P d) p (Set.Icc d.lo d.hi) d.hi := by sorry

end DiscServLine.SPT

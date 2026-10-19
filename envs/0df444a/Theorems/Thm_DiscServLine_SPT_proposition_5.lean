-- Prove2me | Theorems.Thm_DiscServLine_SPT_proposition_5
-- name    : DiscServLine.SPT.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:18:28.262998+00:00
-- url     : https://prove2.me/theorems/0d73e361-d87a-4aa1-962c-8b34aae990d7
-- title:
--   Proposition 5, p. 18 (PDF 18) — under SPT with homogeneous customers the optimal service line has variety, no cutoff and a concave price decreasing at the top
-- statement:
--   Consider the discretionary service line with homogeneous customers ($\Delta=0$: every customer has quality sensitivity $\bar\theta$, service value $\bar\theta t-bt^2$ and waiting cost $c$ per unit of sojourn time), Poisson arrivals of rate $\Lambda$, a single server and non-preemptive SPT. Fix $\bar\theta,b,c$ with $0<c<\bar\theta$ and $b>0$. Then:
--
--   1. For every $\Lambda>0$, the firm's problem (9),
--   $$\max\ (\bar\theta\Lambda_1-b\Lambda_2)-c(\Lambda_1+Q)\quad\text{over feasible service lines},$$
--   has an optimal service line, and every optimal line $(\underline t,\bar t,\mu)$ has (i) service variety, $\underline t<\bar t$; (ii) no customer cutoff, $\Lambda_0=\Lambda$; (iii) a price schedule $P(t)=\bar\theta t-bt^2-c(t+W(t))$ that is concave on $[\underline t,\bar t]$ and decreasing at the top end, $\frac{d}{dt}P(\bar t)<0$.
--   2. There are $\underline\Lambda>0$ and $\bar\Lambda>0$ such that, at every optimal line, $\frac{d}{dt}P(\underline t)<0$ when $\Lambda\in(0,\underline\Lambda)$ and $\frac{d}{dt}P(\underline t)>0$ when $\Lambda\in(\bar\Lambda,\infty)$.
--
--   This is the paper's main result for homogeneous customers: under SPT, operational considerations alone (reducing waiting through the priority rule) make variety optimal, whereas under FIFO the optimal line collapses to a single service.
--
--   **Formalization Note** Service lines are finite demand measures whose support has ends $\underline t,\bar t$, so single services are feasible and (i) is not automatic. Existence of an optimum, presupposed by "the optimal service line design", is stated. Derivatives at $\bar t$ and $\underline t$ are one-sided, within $[\underline t,\bar t]$. The hypotheses $b>0$ and $\Lambda>0$ are added (implicit in the paper).
-- source:
--   Debo & Li, Design and Pricing of Discretionary Service Lines, SSRN working paper 3054741 (Oct. 17, 2017), p. 18 (PDF 18), Proposition 5; proof pp. 43–44 (PDF 43–44)

import Mathlib
import Definitions.Def_DiscServLine_SPT_Model

namespace DiscServLine.SPT

theorem proposition_5 (θbar b c : ℝ) (hc : 0 < c) (hcθ : c < θbar) (hb : 0 < b) :
    (∀ Λ : ℝ, 0 < Λ →
      (∃ d, IsOptimal ⟨θbar, b, c, Λ⟩ d) ∧
      ∀ d, IsOptimal ⟨θbar, b, c, Λ⟩ d →
        d.lo < d.hi ∧ d.Λk 0 = Λ ∧
        ConcaveOn ℝ (Set.Icc d.lo d.hi) (price ⟨θbar, b, c, Λ⟩ d) ∧
        ∃ p < 0, HasDerivWithinAt (price ⟨θbar, b, c, Λ⟩ d) p (Set.Icc d.lo d.hi) d.hi) ∧
    ∃ Λlow Λhigh : ℝ, 0 < Λlow ∧ 0 < Λhigh ∧
      (∀ Λ ∈ Set.Ioo 0 Λlow, ∀ d, IsOptimal ⟨θbar, b, c, Λ⟩ d →
        ∃ p < 0, HasDerivWithinAt (price ⟨θbar, b, c, Λ⟩ d) p (Set.Icc d.lo d.hi) d.lo) ∧
      (∀ Λ ∈ Set.Ioi Λhigh, ∀ d, IsOptimal ⟨θbar, b, c, Λ⟩ d →
        ∃ p > 0, HasDerivWithinAt (price ⟨θbar, b, c, Λ⟩ d) p (Set.Icc d.lo d.hi) d.lo) := by sorry

end DiscServLine.SPT

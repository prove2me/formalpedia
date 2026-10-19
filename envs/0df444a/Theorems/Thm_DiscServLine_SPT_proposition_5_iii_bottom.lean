-- Prove2me | Theorems.Thm_DiscServLine_SPT_proposition_5_iii_bottom
-- name    : DiscServLine.SPT.proposition_5_iii_bottom
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:18:35.205278+00:00
-- url     : https://prove2.me/theorems/8906e7a1-9449-456d-825c-250ae4603427
-- title:
--   Proposition 5 (iii), bottom end, p. 18 (PDF 18) — the price slope at t̲ is negative for small Λ, positive for large Λ
-- statement:
--   Fix $\bar\theta$, $b$, $c$ with $0<c<\bar\theta$ and $b>0$, and let the arrival rate $\Lambda>0$ vary, with $\Delta=0$ and non-preemptive SPT. Then for every $\Lambda>0$ problem (9) has an optimal service line, and there are thresholds $\underline\Lambda>0$ and $\bar\Lambda>0$ such that for every optimal line $(\underline t,\bar t,\mu)$ the price $P(t)=\bar\theta t-bt^2-c(t+W(t))$ satisfies
--   $$\frac{d}{dt}P(\underline t)<0\quad\text{if }\Lambda\in(0,\underline\Lambda),\qquad \frac{d}{dt}P(\underline t)>0\quad\text{if }\Lambda\in(\bar\Lambda,\infty).$$
--
--   In small markets the price decreases at the bottom of the line as well, so it decreases along the whole line; in large markets it rises at the bottom and falls at the top.
--
--   **Formalization Note** The thresholds depend on $(\bar\theta,b,c)$ only. The derivative at $\underline t$ is the one-sided (right) derivative within $[\underline t,\bar t]$. Requiring $\bar\Lambda>0$ loses nothing (a larger threshold also works); $\underline\Lambda>0$ keeps $(0,\underline\Lambda)$ nonempty. Existence of an optimum for every $\Lambda>0$ is stated explicitly.
-- source:
--   Debo & Li, Design and Pricing of Discretionary Service Lines, SSRN working paper 3054741 (Oct. 17, 2017), p. 18 (PDF 18), Proposition 5 (iii), second clause; proof pp. 43–44 (PDF 43–44), (iii-b)

import Mathlib
import Definitions.Def_DiscServLine_SPT_Model

namespace DiscServLine.SPT

theorem proposition_5_iii_bottom (θbar b c : ℝ) (hc : 0 < c) (hcθ : c < θbar) (hb : 0 < b) :
    (∀ Λ : ℝ, 0 < Λ → ∃ d, IsOptimal ⟨θbar, b, c, Λ⟩ d) ∧
      ∃ Λlow Λhigh : ℝ, 0 < Λlow ∧ 0 < Λhigh ∧
        (∀ Λ ∈ Set.Ioo 0 Λlow, ∀ d, IsOptimal ⟨θbar, b, c, Λ⟩ d →
          ∃ p < 0, HasDerivWithinAt (price ⟨θbar, b, c, Λ⟩ d) p (Set.Icc d.lo d.hi) d.lo) ∧
        (∀ Λ ∈ Set.Ioi Λhigh, ∀ d, IsOptimal ⟨θbar, b, c, Λ⟩ d →
          ∃ p > 0, HasDerivWithinAt (price ⟨θbar, b, c, Λ⟩ d) p (Set.Icc d.lo d.hi) d.lo) := by sorry

end DiscServLine.SPT

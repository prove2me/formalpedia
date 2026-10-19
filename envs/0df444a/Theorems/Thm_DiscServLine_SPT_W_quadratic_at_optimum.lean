-- Prove2me | Theorems.Thm_DiscServLine_SPT_W_quadratic_at_optimum
-- name    : DiscServLine.SPT.W_quadratic_at_optimum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:18:39.025891+00:00
-- url     : https://prove2.me/theorems/6250a357-9a02-421e-843e-3f40894a21a0
-- title:
--   Proof of Proposition 5 (iii), p. 43 (PDF 43) — at the optimum W(t) = −α₀ + t²α₂ on [t̲, t̄] with 2α₂t̄ = θ̄/c − 1
-- statement:
--   Assume $0<c<\bar\theta$, $b>0$, $\Lambda>0$, and let $(\underline t,\bar t,\mu)$ be an optimal service line of problem (9). Then the SPT waiting time is quadratic on the service line: there are constants $\alpha_0$ and $\alpha_2>0$ with
--   $$W(t)=-\alpha_0+t^2\alpha_2\quad(\underline t\le t\le\bar t),\qquad 2\alpha_2\bar t=\frac{\bar\theta}{c}-1 .$$
--
--   In the paper $\alpha_0,\alpha_2$ are the Lagrange multipliers of Lemma 3, and the second identity is equation (A–14) with $\alpha_1=\bar\theta/c-1$. The paper's proof of Proposition 5 (iii) derives the concavity of the price and its slope at $\bar t$ from these two facts.
-- source:
--   Debo & Li, Design and Pricing of Discretionary Service Lines, SSRN working paper 3054741 (Oct. 17, 2017), p. 43 (PDF 43), proof of Proposition 5 (iii) and (iii-a); Lemma 3 (i), p. 16 (PDF 16)

import Mathlib
import Definitions.Def_DiscServLine_SPT_Model

namespace DiscServLine.SPT

theorem W_quadratic_at_optimum (P : Params) (hP : P.Standing) (d : Design)
    (hd : IsOptimal P d) :
    ∃ α0 α2 : ℝ, 0 < α2 ∧ (∀ t ∈ Set.Icc d.lo d.hi, d.W t = -α0 + t ^ 2 * α2) ∧
      2 * α2 * d.hi = P.θbar / P.c - 1 := by sorry

end DiscServLine.SPT

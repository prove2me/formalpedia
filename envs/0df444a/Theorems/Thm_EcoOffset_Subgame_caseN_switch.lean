-- Prove2me | Theorems.Thm_EcoOffset_Subgame_caseN_switch
-- name    : EcoOffset.Subgame.caseN_switch
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:27:15.791718+00:00
-- url     : https://prove2.me/theorems/21162146-a409-4e0c-9331-aad7c1fec7c5
-- title:
--   Proof of Proposition 1, Online Supplement p. 24 (PDF 57) — Case N: the best response switches from selling to all (below X) to selling at vh (above X)
-- statement:
--   Assume the standing assumptions of the model, Case N ($\beta_u=1$), $\alpha>0$, $\beta_c<B_2$, and let $X>0$ be the least zero of $h$ ($h(X)=0$, $h>0$ on $[0,X)$). Assume further that $h$ changes sign at $X$ (every right neighbourhood of $X$ contains a $g$ with $h(g)<0$), that $X<\xi$, and condition (1):
--   $$\pi(v_l,e_{X,1},e_{X,1}+e_o\mid X)>\pi(v_h,\bar e,0\mid X)=(v_h-c(\bar e))(1-\alpha)m.$$
--   Then:
--   1. there is $\epsilon\in(0,X)$ such that for every $g\in(X-\epsilon,X)$ the best responses to $g$ are exactly $p^*=v_l$, $e^*=e_{g,1}$, $t^*=e_{g,1}+e_o$;
--   2. for every $\epsilon>0$ there is $g\in(X,X+\epsilon)$ at which the best responses are exactly $p^*=v_h$, $e^*=e_{g,1-\alpha+\alpha\beta_c}$, $t^*=e_{g,1-\alpha+\alpha\beta_c}+e_o$.
--
--   Just below $X$ the firm covers the whole market; just above, it drops the low-value eco-conscious consumers. This switch is what drives Proposition 1(i).
--
--   **Formalization Note** The page claims item 1 on all of $(0,X)$ and item 2 on a whole interval $(X,X+\epsilon)$; it proves neither, and condition (1) only controls prices near $X$. The statement keeps the left neighbourhood, and the right side in the form that follows from the sign-change hypothesis, which stands in for the page's unproved $\partial h/\partial g|_{g=X}<0$. The page's "then we must have $X<G$" is not proved there and is replaced by the hypothesis $X<\xi$.
-- source:
--   Gao & Souza, Carbon Offsetting with Eco-Conscious Consumers, SSRN 3440652 (copy held, sha256 e7d7f85a…7306), Online Supplement p. 24 (PDF 57), proof of Proposition 1, condition (1) and the two bullets

import Mathlib
import Definitions.Def_EcoOffset_Subgame_Model

namespace EcoOffset.Subgame

/-- Proof of Proposition 1, Online Supplement p. 24: in Case N, under the hypotheses of
Proposition 1(i), just below `X` the best responses are exactly `(vl, e_{g,1}, e_{g,1} + eo)`, and
arbitrarily close above `X` there are prices at which the best responses are exactly
`(vh, e_{g,aN}, e_{g,aN} + eo)`. -/
theorem caseN_switch (P : Params) (hS : P.Standing) (hβu : P.βu = 1) (hα : 0 < P.α)
    (hB2 : P.βc < B2 P) (X : ℝ) (hX : 0 < X) (hX0 : hN P X = 0)
    (hXmin : ∀ g ∈ Set.Ico 0 X, 0 < hN P g)
    (hsign : ∀ ε > 0, ∃ g ∈ Set.Ioo X (X + ε), hN P g < 0)
    (hXξ : X < P.ξ) (hcond : valOne P < valAll P X) :
    (∃ ε, 0 < ε ∧ ε < X ∧ ∀ g ∈ Set.Ioo (X - ε) X, ∀ p e t,
      IsBestResponse P g p e t ↔ (p = P.vl ∧ e = segOpt P g 1 ∧ t = segOpt P g 1 + P.eo)) ∧
    (∀ ε > 0, ∃ g ∈ Set.Ioo X (X + ε), ∀ p e t,
      IsBestResponse P g p e t ↔
        (p = P.vh ∧ e = segOpt P g (aN P) ∧ t = segOpt P g (aN P) + P.eo)) := by sorry

end EcoOffset.Subgame

-- Prove2me | Theorems.Thm_EcoOffset_Subgame_caseP_switch
-- name    : EcoOffset.Subgame.caseP_switch
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:27:12.093076+00:00
-- url     : https://prove2.me/theorems/562b2e7e-6e11-4526-b4ca-04e609e53c9d
-- title:
--   Proof of Proposition 1, Online Supplement p. 25 (PDF 58) — Case P: the best response switches from selling to all (below X) to selling at vh (above X)
-- statement:
--   Assume the standing assumptions of the model, Case P ($\beta_c=1$), $\alpha<1$, $v_h-v_l<\xi e_o$ and $\beta_u<\tilde B_2$, and let $X>0$ be the least zero of the Case P function $h$. Assume further that $h$ changes sign at $X$ (every right neighbourhood of $X$ contains a $g$ with $h(g)<0$), that $X<\xi$, and condition (1):
--   $$\pi(v_h,e_{X,a_P},e_{X,a_P}+e_o\mid X)>\max\big((v_h-c(\bar e))(1-\alpha)\beta_u m,\ (v_l-c(\bar e))(1-\alpha)m\big),\qquad a_P=\alpha+(1-\alpha)\beta_u.$$
--   Then:
--   1. there is $\epsilon\in(0,X)$ such that for every $g\in(X-\epsilon,X)$ the best responses are exactly $p^*=v_l$, $e^*=e_{g,1}$, $t^*=e_{g,1}+e_o-\frac{v_h-v_l}{\xi}$;
--   2. for every $\epsilon>0$ there is $g\in(X,X+\epsilon)$ at which the best responses are exactly $p^*=v_h$, $e^*=e_{g,a_P}$, $t^*=e_{g,a_P}+e_o$.
--
--   Just below $X$ the firm covers the whole market; just above, it drops the low-value eco-unconscious consumers. This switch drives Proposition 1(ii).
--
--   **Formalization Note** As in Case N: item 1 is stated on a left neighbourhood of $X$ rather than all of $(0,X)$, the sign-change hypothesis stands in for the page's unproved $\partial h/\partial g|_{g=X}<0$, and $X<\xi$ replaces the page's unproved "then we must have $X<G$".
-- source:
--   Gao & Souza, Carbon Offsetting with Eco-Conscious Consumers, SSRN 3440652 (copy held, sha256 e7d7f85a…7306), Online Supplement p. 25 (PDF 58), proof of Proposition 1, Case P, condition (1) and the two bullets

import Mathlib
import Definitions.Def_EcoOffset_Subgame_Model

namespace EcoOffset.Subgame

/-- Proof of Proposition 1, Online Supplement p. 25: in Case P, under the hypotheses of
Proposition 1(ii), just below `X` the best responses are exactly
`(vl, e_{g,1}, e_{g,1} + eo − (vh − vl)/ξ)`, and arbitrarily close above `X` there are prices at
which the best responses are exactly `(vh, e_{g,aP}, e_{g,aP} + eo)`. -/
theorem caseP_switch (P : Params) (hS : P.Standing) (hβc : P.βc = 1) (hα : P.α < 1)
    (hv : P.vh - P.vl < P.ξ * P.eo) (hB2 : P.βu < B2P P)
    (X : ℝ) (hX : 0 < X) (hX0 : hP P X = 0) (hXmin : ∀ g ∈ Set.Ico 0 X, 0 < hP P g)
    (hsign : ∀ ε > 0, ∃ g ∈ Set.Ioo X (X + ε), hP P g < 0)
    (hXξ : X < P.ξ) (hcond : max (valOne P) (valThree P) < valTwoP P X) :
    (∃ ε, 0 < ε ∧ ε < X ∧ ∀ g ∈ Set.Ioo (X - ε) X, ∀ p e t,
      IsBestResponse P g p e t ↔
        (p = P.vl ∧ e = segOpt P g 1 ∧ t = segOpt P g 1 + P.eo - (P.vh - P.vl) / P.ξ)) ∧
    (∀ ε > 0, ∃ g ∈ Set.Ioo X (X + ε), ∀ p e t,
      IsBestResponse P g p e t ↔
        (p = P.vh ∧ e = segOpt P g (aP P) ∧ t = segOpt P g (aP P) + P.eo)) := by sorry

end EcoOffset.Subgame

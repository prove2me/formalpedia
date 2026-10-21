-- Prove2me | Theorems.Thm_EcoOffset_Subgame_caseP_condition1
-- name    : EcoOffset.Subgame.caseP_condition1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:27:13.012986+00:00
-- url     : https://prove2.me/theorems/10919601-63af-43db-a088-402067645712
-- title:
--   Proof of Proposition 1, Online Supplement pp. 25–26 (PDF 58–59) — Case P: condition (1) reduces to beating π(vl, ē, 0) and is equivalent to βu being large
-- statement:
--   Assume the standing assumptions of the model, Case P ($\beta_c=1$), $\alpha<1$ and $\beta_u<\tilde B_2$. Write $a_P=\alpha+(1-\alpha)\beta_u$ and $\Pi_2(X)=\pi(v_h,e_{X,a_P},e_{X,a_P}+e_o\mid X)$.
--   1. $(v_h-c(\bar e))(1-\alpha)\beta_u m<(v_l-c(\bar e))(1-\alpha)m$, so for every $X$, condition (1) is equivalent to
--   $$\Pi_2(X)>(v_l-c(\bar e))(1-\alpha)m.$$
--   2. Suppose also $v_h-v_l<\xi e_o$. Let $\beta_u\le\beta_u'<\tilde B_2$, and let the model with $\beta_u$ replaced by $\beta_u'$ (all else unchanged) have least zero $X'>0$ of $h$, while the original has least zero $X>0$. If condition (1) holds for $\beta_u$ at $X$, then $X'\le X$ and condition (1) holds for $\beta_u'$ at $X'$.
--
--   Item 2 says the set of admissible $\beta_u$ satisfying condition (1) is an upper set, i.e. of the form $\beta_u>\tilde B_1$, which is the lower threshold of Proposition 1(ii).
--
--   **Formalization Note** The page's derivative and envelope-theorem argument is recorded as the resulting weak monotonicity, without derivatives.
-- source:
--   Gao & Souza, Carbon Offsetting with Eco-Conscious Consumers, SSRN 3440652 (copy held, sha256 e7d7f85a…7306), Online Supplement pp. 25–26 (PDF 58–59), proof of Proposition 1, Case P ('As for condition (1) … condition (1) is equivalent to βu being large (i.e., βu > ˜B1)')

import Mathlib
import Definitions.Def_EcoOffset_Subgame_Model

namespace EcoOffset.Subgame

/-- Proof of Proposition 1, Online Supplement pp. 25–26: in Case P, `βu < ˜B2` gives
`π(vh, ¯e, 0) < π(vl, ¯e, 0)`, so condition (1) reduces to
`π(vh, e_{X,aP}, e_{X,aP} + eo | X) > (vl − c(¯e))(1 − α) m`; and "condition (1) is equivalent to
βu being large": raising `βu` (below `˜B2`, all other primitives fixed) moves the least zero `X`
of `h` weakly down, and condition (1) persists. -/
theorem caseP_condition1 (P : Params) (hS : P.Standing) (hβc : P.βc = 1) (hα : P.α < 1)
    (hB2 : P.βu < B2P P) :
    (valOne P < valThree P ∧
      ∀ X : ℝ, max (valOne P) (valThree P) < valTwoP P X ↔ valThree P < valTwoP P X) ∧
    (P.vh - P.vl < P.ξ * P.eo →
      ∀ βu' : ℝ, P.βu ≤ βu' → βu' < B2P P →
      ∀ X X' : ℝ, 0 < X → hP P X = 0 → (∀ g ∈ Set.Ico 0 X, 0 < hP P g) →
        0 < X' → hP { P with βu := βu' } X' = 0 →
        (∀ g ∈ Set.Ico 0 X', 0 < hP { P with βu := βu' } g) →
        max (valOne P) (valThree P) < valTwoP P X →
        X' ≤ X ∧
          max (valOne { P with βu := βu' }) (valThree { P with βu := βu' }) <
            valTwoP { P with βu := βu' } X') := by sorry

end EcoOffset.Subgame

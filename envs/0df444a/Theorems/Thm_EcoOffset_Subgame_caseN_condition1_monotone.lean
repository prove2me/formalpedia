-- Prove2me | Theorems.Thm_EcoOffset_Subgame_caseN_condition1_monotone
-- name    : EcoOffset.Subgame.caseN_condition1_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:27:11.473674+00:00
-- url     : https://prove2.me/theorems/8425c9eb-92de-478d-b353-368e8c2209ad
-- title:
--   Proof of Proposition 1, Online Supplement p. 24 (PDF 57) — Case N: condition (1) is equivalent to βc being large (βc > B1)
-- statement:
--   Assume the standing assumptions of the model, Case N ($\beta_u=1$) and $\alpha>0$. Let $\beta_c\le\beta_c'<B_2$, and let $P'$ be the model with $\beta_c$ replaced by $\beta_c'$ and every other primitive unchanged. Let $X>0$ be the least zero of $h$ for $\beta_c$ and $X'>0$ the least zero of $h$ for $\beta_c'$. If condition (1) holds for $\beta_c$ at $X$,
--   $$\pi(v_l,e_{X,1},e_{X,1}+e_o\mid X)>(v_h-c(\bar e))(1-\alpha)m,$$
--   then
--   $$X'\le X\qquad\text{and condition (1) holds for }\beta_c'\text{ at }X'.$$
--
--   So the set of $\beta_c<B_2$ for which condition (1) holds is an upper set: it has the form $\beta_c>B_1$ (or $\ge B_1$), which is the lower threshold of Proposition 1(i).
--
--   **Formalization Note** The page argues with $\partial h/\partial\beta_c<0$, $\partial h/\partial g|_{g=X}<0$ and the envelope theorem; the statement records the resulting monotonicity, in weak form, without derivatives.
-- source:
--   Gao & Souza, Carbon Offsetting with Eco-Conscious Consumers, SSRN 3440652 (copy held, sha256 e7d7f85a…7306), Online Supplement p. 24 (PDF 57), proof of Proposition 1 ('As for condition (1) … condition (1) is equivalent to βc being large (i.e., βc > B1)')

import Mathlib
import Definitions.Def_EcoOffset_Subgame_Model

namespace EcoOffset.Subgame

/-- Proof of Proposition 1, Online Supplement p. 24, "condition (1) is equivalent to βc being
large": in Case N, raising `βc` (below `B2`, all other primitives fixed) moves the least zero `X`
of `h` weakly down, and condition (1) at `X` persists. -/
theorem caseN_condition1_monotone (P : Params) (hS : P.Standing) (hβu : P.βu = 1)
    (hα : 0 < P.α) (βc' : ℝ) (hle : P.βc ≤ βc') (hlt : βc' < B2 P)
    (X X' : ℝ) (hX : 0 < X) (hX0 : hN P X = 0) (hXmin : ∀ g ∈ Set.Ico 0 X, 0 < hN P g)
    (hX' : 0 < X') (hX'0 : hN { P with βc := βc' } X' = 0)
    (hX'min : ∀ g ∈ Set.Ico 0 X', 0 < hN { P with βc := βc' } g)
    (hcond : valOne P < valAll P X) :
    X' ≤ X ∧ valOne { P with βc := βc' } < valAll { P with βc := βc' } X' := by sorry

end EcoOffset.Subgame

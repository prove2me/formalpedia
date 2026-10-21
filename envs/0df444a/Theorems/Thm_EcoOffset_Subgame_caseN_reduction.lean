-- Prove2me | Theorems.Thm_EcoOffset_Subgame_caseN_reduction
-- name    : EcoOffset.Subgame.caseN_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:27:05.156596+00:00
-- url     : https://prove2.me/theorems/417397c5-dc83-458c-a873-56a6d4f8bc34
-- title:
--   Proof of Proposition 1, Online Supplement p. 24 (PDF 57), with Online Supplement I1 — Case N: with offsets the subgame equilibrium is one of two profiles
-- statement:
--   Assume the standing assumptions of the model and Case N, $\beta_u=1$. Let $0<g<\xi$ and $a_N=1-\alpha+\alpha\beta_c$. Write
--   $$\Pi_1=(v_h-c(\bar e))(1-\alpha)\beta_u m,\quad \Pi_2(g)=\pi(v_h,e_{g,a_N},e_{g,a_N}+e_o\mid g),\quad \Pi_6(g)=\pi(v_l,e_{g,1},e_{g,1}+e_o\mid g).$$
--   Then:
--   1. every feasible $(p,e,t)$ satisfies $\pi(p,e,t\mid g)\le\max(\Pi_1,\Pi_2(g),\Pi_6(g))$;
--   2. if $\Pi_6(g)$ is strictly the largest of the three, the best responses to $g$ are exactly the single profile $(v_l,\,e_{g,1},\,e_{g,1}+e_o)$;
--   3. if $\Pi_2(g)$ is strictly the largest, the best responses are exactly $(v_h,\,e_{g,a_N},\,e_{g,a_N}+e_o)$;
--   4. at $(v_l,e_{g,1},e_{g,1}+e_o)$ the demands are $d_c=\alpha m$, $d_u=(1-\alpha)m$; at $(v_h,e_{g,a_N},e_{g,a_N}+e_o)$ they are $d_c=\alpha\beta_c m$, $d_u=(1-\alpha)m$.
--
--   This is the reduction of the firm's problem to the six options of Online Supplement I1, specialized to Case N: when the firm offsets, it either sells to the high-value consumers at $v_h$ or to everyone at $v_l$, and in both cases it offsets its whole footprint.
--
--   **Formalization Note** The page's "if $t>0$, the equilibrium must be one of the following" is stated as an upper bound on all profits plus a characterization of the best responses when one profile is strictly optimal; the option without offsets enters through $\Pi_1$.
-- source:
--   Gao & Souza, Carbon Offsetting with Eco-Conscious Consumers, SSRN 3440652 (copy held, sha256 e7d7f85a…7306), Online Supplement p. 24 (PDF 57), proof of Proposition 1, list 1–2; Online Supplement pp. 1–2 (PDF 34–35), I1, options 1–6

import Mathlib
import Definitions.Def_EcoOffset_Subgame_Model

namespace EcoOffset.Subgame

/-- Proof of Proposition 1, Online Supplement p. 24 (with Online Supplement I1): in Case N
(`βu = 1`), for `0 < g < ξ` every feasible profit is at most the largest of `π(vh, ¯e, 0)`,
`π(vh, e_{g,aN}, e_{g,aN} + eo)` and `π(vl, e_{g,1}, e_{g,1} + eo)`; when one of the last two is
strictly largest, the best responses are exactly the corresponding profile; and the demands at
those profiles are `(d_c, d_u) = (αm, (1 − α)m)` and `(αβc m, (1 − α)m)`. -/
theorem caseN_reduction (P : Params) (hS : P.Standing) (hβu : P.βu = 1) (g : ℝ)
    (hg0 : 0 < g) (hgξ : g < P.ξ) :
    (∀ p e t, Feasible P e t →
      profit P g p e t ≤ max (max (valOne P) (valTwoN P g)) (valAll P g)) ∧
    (max (valOne P) (valTwoN P g) < valAll P g →
      ∀ p e t, IsBestResponse P g p e t ↔
        (p = P.vl ∧ e = segOpt P g 1 ∧ t = segOpt P g 1 + P.eo)) ∧
    (max (valOne P) (valAll P g) < valTwoN P g →
      ∀ p e t, IsBestResponse P g p e t ↔
        (p = P.vh ∧ e = segOpt P g (aN P) ∧ t = segOpt P g (aN P) + P.eo)) ∧
    (demandC P P.vl (segOpt P g 1) (segOpt P g 1 + P.eo) = P.α * P.m ∧
      demandU P P.vl (segOpt P g 1) (segOpt P g 1 + P.eo) = (1 - P.α) * P.m) ∧
    (demandC P P.vh (segOpt P g (aN P)) (segOpt P g (aN P) + P.eo) = P.α * P.βc * P.m ∧
      demandU P P.vh (segOpt P g (aN P)) (segOpt P g (aN P) + P.eo) = (1 - P.α) * P.m) := by sorry

end EcoOffset.Subgame

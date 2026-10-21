-- Prove2me | Theorems.Thm_EcoOffset_Subgame_caseP_reduction
-- name    : EcoOffset.Subgame.caseP_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:27:02.513022+00:00
-- url     : https://prove2.me/theorems/15789b3e-810a-4909-8428-6398d092cab2
-- title:
--   Proof of Proposition 1, Online Supplement p. 25 (PDF 58), with Online Supplement I1 — Case P: with offsets the subgame equilibrium is one of two profiles
-- statement:
--   Assume the standing assumptions of the model, Case P ($\beta_c=1$) and $v_h-v_l<\xi e_o$. Let $0<g<\xi$ and $a_P=\alpha+(1-\alpha)\beta_u$. Write
--   $$\Pi_1=(v_h-c(\bar e))(1-\alpha)\beta_u m,\qquad \Pi_3=(v_l-c(\bar e))(1-\alpha)m,$$
--   $$\Pi_2(g)=\pi(v_h,e_{g,a_P},e_{g,a_P}+e_o\mid g),\qquad \tilde\Pi(g)=\pi\big(v_l,e_{g,1},e_{g,1}+e_o-\tfrac{v_h-v_l}{\xi}\;\big|\;g\big).$$
--   Then:
--   1. every feasible $(p,e,t)$ satisfies $\pi(p,e,t\mid g)\le\max(\Pi_1,\Pi_3,\Pi_2(g),\tilde\Pi(g))$;
--   2. if $\tilde\Pi(g)$ is strictly the largest, the best responses are exactly $(v_l,\,e_{g,1},\,e_{g,1}+e_o-\frac{v_h-v_l}{\xi})$;
--   3. if $\Pi_2(g)$ is strictly the largest, the best responses are exactly $(v_h,\,e_{g,a_P},\,e_{g,a_P}+e_o)$;
--   4. at $(v_h,e_{g,a_P},e_{g,a_P}+e_o)$ the demands are $d_c=\alpha m$, $d_u=(1-\alpha)\beta_u m$; at $(v_l,e_{g,1},e_{g,1}+e_o-\frac{v_h-v_l}{\xi})$ they are $d_c=\alpha m$, $d_u=(1-\alpha)m$.
--
--   In Case P, covering the whole market at the price $v_l$ only requires the footprint to fall to $(v_h-v_l)/\xi$, so the firm offsets less than its whole footprint; selling at $v_h$ still requires a zero footprint.
--
--   **Formalization Note** As in Case N, "the equilibrium must be one of the following" is stated as an upper bound on all profits plus a characterization of best responses when one profile is strictly optimal; the options without offsets enter through $\Pi_1$ and $\Pi_3$.
-- source:
--   Gao & Souza, Carbon Offsetting with Eco-Conscious Consumers, SSRN 3440652 (copy held, sha256 e7d7f85a…7306), Online Supplement p. 25 (PDF 58), proof of Proposition 1, Case P, list 1–2; Online Supplement pp. 1–2 (PDF 34–35), I1, options 1–6

import Mathlib
import Definitions.Def_EcoOffset_Subgame_Model

namespace EcoOffset.Subgame

/-- Proof of Proposition 1, Online Supplement p. 25 (with Online Supplement I1): in Case P
(`βc = 1`) with `vh − vl < ξ eo`, for `0 < g < ξ` every feasible profit is at most the largest of
`π(vh, ¯e, 0)`, `π(vl, ¯e, 0)`, `π(vh, e_{g,aP}, e_{g,aP} + eo)` and
`π(vl, e_{g,1}, e_{g,1} + eo − (vh − vl)/ξ)`; when one of the last two is strictly largest, the
best responses are exactly the corresponding profile; and the demands at those profiles are
`(αm, (1 − α)βu m)` and `(αm, (1 − α)m)`. -/
theorem caseP_reduction (P : Params) (hS : P.Standing) (hβc : P.βc = 1)
    (hv : P.vh - P.vl < P.ξ * P.eo) (g : ℝ) (hg0 : 0 < g) (hgξ : g < P.ξ) :
    (∀ p e t, Feasible P e t →
      profit P g p e t ≤ max (max (valOne P) (valThree P)) (max (valTwoP P g) (valAllP P g))) ∧
    (max (max (valOne P) (valThree P)) (valTwoP P g) < valAllP P g →
      ∀ p e t, IsBestResponse P g p e t ↔
        (p = P.vl ∧ e = segOpt P g 1 ∧
          t = segOpt P g 1 + P.eo - (P.vh - P.vl) / P.ξ)) ∧
    (max (max (valOne P) (valThree P)) (valAllP P g) < valTwoP P g →
      ∀ p e t, IsBestResponse P g p e t ↔
        (p = P.vh ∧ e = segOpt P g (aP P) ∧ t = segOpt P g (aP P) + P.eo)) ∧
    (demandC P P.vh (segOpt P g (aP P)) (segOpt P g (aP P) + P.eo) = P.α * P.m ∧
      demandU P P.vh (segOpt P g (aP P)) (segOpt P g (aP P) + P.eo) =
        (1 - P.α) * P.βu * P.m) ∧
    (demandC P P.vl (segOpt P g 1) (segOpt P g 1 + P.eo - (P.vh - P.vl) / P.ξ) = P.α * P.m ∧
      demandU P P.vl (segOpt P g 1) (segOpt P g 1 + P.eo - (P.vh - P.vl) / P.ξ) =
        (1 - P.α) * P.m) := by sorry

end EcoOffset.Subgame

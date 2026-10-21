-- Prove2me | Theorems.Thm_CapacityRights_Gatekeeper_claim_lemma_1
-- name    : CapacityRights.Gatekeeper.claim_lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:38:59.205402+00:00
-- url     : https://prove2.me/theorems/98cfc30f-5794-421e-9d24-683cb8a7cdea
-- title:
--   Claim in proof of Lemma 1: derivative of stand-alone margin
-- statement:
--   Fix a positive capacity $k$ and a realized Division 1 shock $\epsilon_1$ in its support. Let $q^o_1$ be any output maximizing $R_1(q,\epsilon_1)-w_1q$ over $0\le q\le k$. Then the maximized stand-alone margin is differentiable at $k$, and
--
--   $$
--   \frac{\partial}{\partial k}CM_1(k\mid w_1,\epsilon_1)=R'_1(q^o_1,\epsilon_1)-w_1.
--   $$
--
--   The claim identifies the marginal value of a unit of dedicated capacity. It supplies the stand-alone marginal term used in the gatekeeper first-order condition.
--
--   **Formalization Note** The derivative is stated at $k>0$; the boundary $k=0$ uses a one-sided derivative in later definitions. Every maximizing output is covered, without choosing one.
-- source:
--   Dutta & Reichelstein, Capacity Rights and Full Cost Transfer Pricing, CESifo Working Paper No. 7968 (November 2019), p. 36 (PDF 39), Claim in proof of Lemma 1

import Mathlib
import Definitions.Def_CapacityRights_Gatekeeper_Model

namespace CapacityRights.Gatekeeper

open MeasureTheory

/-- Claim in the proof of Lemma 1, p. 36 (PDF 39). -/
theorem claim_lemma_1 (E : Env) (hS : E.Standing)
    (k e1 q : ℝ) (hk : 0 < k) (he : e1 ∈ Set.Icc E.a1 E.b1)
    (hq : IsSoloOpt1 E k e1 q) :
    HasDerivAt (fun x => CM1 E x e1) (deriv (fun x => E.R1 x e1) q - E.w1) k := by sorry

end CapacityRights.Gatekeeper

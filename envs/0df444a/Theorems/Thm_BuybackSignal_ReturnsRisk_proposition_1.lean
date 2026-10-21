-- Prove2me | Theorems.Thm_BuybackSignal_ReturnsRisk_proposition_1
-- name    : BuybackSignal.ReturnsRisk.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:50:48.213907+00:00
-- url     : https://prove2.me/theorems/097ebfec-84f9-4ada-9c26-d00c3a92025e
-- title:
--   Proposition 1, p. 13 — the most efficient separating equilibrium
-- statement:
--   Problem (4) has a maximizing contract. Every solution $(\bar w^\star,\bar r^\star)$, paired with the riskier type's full-information contract $(w^\circ,r^\circ(\underline\theta))$ and the paper's pessimistic off-path belief, forms a separating perfect Bayesian equilibrium. Both types' deviations are checked. In this equilibrium,
--   $$
--   \bar w^\star<w^\circ,\qquad
--   \bar r^\star<r^\circ(\bar\theta)<r^\circ(\underline\theta),\qquad
--   \bar s^\star<s^\circ,\qquad \bar q^\star<q^\circ.
--   $$
--   No inventory remains after high demand. This is the paper's returns-risk signaling result.
--
--   **Formalization Note** “Most efficient” uses the operational profile defined by problem (4) and the specified beliefs. The intuitive-criterion refinement is not part of this item.
-- source:
--   Wang, Gurnani & Subramanian, The Informational Role of Buyback Contracts, SSRN 3166462 (author's revised version; Management Science 2020), p. 13 (PDF 13), Proposition 1 and problem (4); proof EC p. 15 (PDF 47)

import Mathlib
import Definitions.Def_BuybackSignal_ReturnsRisk_Model

namespace BuybackSignal.ReturnsRisk

theorem proposition_1 (P : Params) (hP : P.Standing) :
    (∃ c : ℝ × ℝ, P.IsSolution4 c) ∧
    ∀ c : ℝ × ℝ, P.IsSolution4 c →
      P.IsSeparatingPBE c (P.w0, P.r0 P.θlow) (P.pessimistic c) ∧
      c.1 < P.w0 ∧ c.2 < P.r0 P.θbar ∧
      P.r0 P.θbar < P.r0 P.θlow ∧
      P.sR c.1 c.2 P.θbar P.lam < P.s0 ∧
      P.unsoldLow c.1 c.2 P.θbar P.lam < P.q0 ∧
      P.unsoldHigh (P.sR c.1 c.2 P.θbar P.lam) c.2 P.θbar = 0 := by sorry
end BuybackSignal.ReturnsRisk

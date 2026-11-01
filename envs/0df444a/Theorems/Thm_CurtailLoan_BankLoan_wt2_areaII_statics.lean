-- Prove2me | Theorems.Thm_CurtailLoan_BankLoan_wt2_areaII_statics
-- name    : CurtailLoan.BankLoan.wt2_areaII_statics
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-31T13:45:04.566296+00:00
-- url     : https://prove2.me/theorems/1a1aad3d-39d3-45b0-b3e6-58db882ca8b4
-- title:
--   Proof of Proposition 2 (2), Appendix p. 30 (PDF 63), with Proposition A.8 — in Area II, $w^t_2$ strictly decreases with $u$ and strictly increases with $\tau$
-- statement:
--   Consider the model of the mission with a regular demand law (density $f$, IGFR). Let $w^t_2$ be the larger root of $t_k(w)=t$ on $(w^u_1,w^u_2)$, i.e. the right end of $\{w\in(w^u_1,w^u_2): t\le t_k(w)\}$.
--
--   1. **Initial loan limit.** If $u_1<u_2$ and, for every $u\in[u_1,u_2]$ (all other parameters fixed), the standing assumptions of Propositions 1–2 hold (the global assumptions together with $u+l-\tau<w^EQ^E$) and the fixed premium lies in Area II, $t_k(w_I)<t\le t_k(w_{II})$, then
--   $$w^t_2(u_2)<w^t_2(u_1).$$
--   2. **Fixed bank fee.** If $\tau_1<\tau_2$ and the same assumptions and Area II hold for every $\tau\in[\tau_1,\tau_2]$, then
--   $$w^t_2(\tau_1)<w^t_2(\tau_2).$$
--
--   This is the comparative statics of the equilibrium price $w^*=w^t_2$ used in the proof of Proposition 2 (2) ("$w^t_2$ decreases with $u$"), which cites Proposition A.8 ("$w^t_2$ decreases with $l$, $u$ and $t$, increases with $\tau$").
--
--   **Formalization note.** Proposition A.8 (milestone `proposition_A8_moreover`) is stated under $t<t_k(w_{\min})$; Area II only gives $t\le t_k(w_{II})\le t_k(w_{\min})$, and equality $t=t_k(w_{\min})$ can occur at the endpoint $u_2$ (resp. $\tau_1$) of the segment. This lemma states the monotonicity under exactly the hypotheses of Proposition 2 part 2. Expected route: apply Proposition A.8 on a sub-segment where $t<t_k(w_{\min})$ holds (it does at every interior point, because $t_k$ strictly decreases with $u$ and increases with $\tau$, Lemma A.7), and handle the endpoint by the monotone inclusion of the sets $\{w: t\le t_k(w)\}$.
-- source:
--   Wang & Cai, Curtailing bank loan and loan insurance under risk regulations in supply chain finance, SSRN 3760840 (forthcoming Management Science 2023; PDF of 2023-02-24), Appendix p. 30 (PDF 63), proof of Proposition 2 (2) ('w^t_2 decreases with u'); Appendix p. 23 (PDF 56), Proposition A.8, Moreover ('w^t_2 decreases with l, u and t, increases with tau')

import Mathlib
import Definitions.Def_SupplyChainTheory_contracts
import Definitions.Def_CurtailLoan_BankLoan_Model

namespace CurtailLoan.BankLoan

theorem wt2_areaII_statics (P : Params) (hR : P.Regular) :
    (∀ u₁ u₂ : ℝ, u₁ < u₂ →
      (∀ x ∈ Set.Icc u₁ u₂, Standing (P.withU x) ∧ AreaII (P.withU x)) →
      wt2 (P.withU u₂) < wt2 (P.withU u₁)) ∧
    (∀ τ₁ τ₂ : ℝ, τ₁ < τ₂ →
      (∀ x ∈ Set.Icc τ₁ τ₂, Standing (P.withTau x) ∧ AreaII (P.withTau x)) →
      wt2 (P.withTau τ₁) < wt2 (P.withTau τ₂)) := by sorry

end CurtailLoan.BankLoan

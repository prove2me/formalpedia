-- Prove2me | Theorems.Thm_CurtailLoan_BankLoan_lemma_A9_1
-- name    : CurtailLoan.BankLoan.lemma_A9_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:16:16.409627+00:00
-- url     : https://prove2.me/theorems/cc225abc-7577-453c-a61a-84ad05317e8a
-- title:
--   Lemma A.9 (1), first clause, Appendix p. 22 (PDF 55) — $w_s$ increases with $c$ and with $u$
-- statement:
--   Consider the model of the mission with a regular demand law, and let $w_s$ be the supplier's acceptable minimal wholesale price: the smallest $w \in (w^u_1, w^u_2)$ with
--   $$(w - c)\min\Bigl(S^{-1}\bigl(v + S(\tfrac{u+l-\tau}{w}) - u\bigr),\ \bar F^{-1}(w)\Bigr) \ge (w^u_2 - c)\bar F^{-1}(w^u_2).$$
--
--   1. If $c_1 < c_2$ and the standing assumptions (which include $u + l - \tau < w^E Q^E$) hold for every unit cost $c \in [c_1, c_2]$, then $w_s|_{c = c_1} < w_s|_{c = c_2}$.
--   2. If $u_1 < u_2$ and the standing assumptions hold for every initial loan limit $u \in [u_1, u_2]$, then $w_s|_{u = u_1} < w_s|_{u = u_2}$.
--
--   $w_s$ enters the upper boundary $t_k(w_{II})$, $w_{II} = \max(w_s, w_{min})$, of the insurance-cooperation region.
--
--   **Formalization Note** "Increases" is strict and is read along parameter segments on which the hypotheses hold pointwise. The remaining clauses of Lemma A.9 (the dependence on $v$ and part (2) with the threshold $c_0$) are not formalized.
-- source:
--   Wang & Cai, Curtailing bank loan and loan insurance under risk regulations in supply chain finance, SSRN 3760840 (forthcoming Management Science 2023; PDF of 2023-02-24), Appendix p. 22 (PDF 55), Lemma A.9 (1), first clause; w_s defined on Appendix p. 21 (PDF 54)

import Mathlib
import Definitions.Def_SupplyChainTheory_contracts
import Definitions.Def_CurtailLoan_BankLoan_Model

namespace CurtailLoan.BankLoan

/-- Lemma A.9 (1), first clause, Appendix p. 22 (PDF 55): `w_s` strictly increases with `c` and
with `u`. -/
theorem lemma_A9_1 (P : Params) (hR : P.Regular) :
    (∀ c₁ c₂ : ℝ, c₁ < c₂ → (∀ x ∈ Set.Icc c₁ c₂, Standing (P.withC x)) →
      ws (P.withC c₁) < ws (P.withC c₂)) ∧
    (∀ u₁ u₂ : ℝ, u₁ < u₂ → (∀ x ∈ Set.Icc u₁ u₂, Standing (P.withU x)) →
      ws (P.withU u₁) < ws (P.withU u₂)) := by sorry

end CurtailLoan.BankLoan

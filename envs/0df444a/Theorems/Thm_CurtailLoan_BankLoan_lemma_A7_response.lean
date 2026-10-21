-- Prove2me | Theorems.Thm_CurtailLoan_BankLoan_lemma_A7_response
-- name    : CurtailLoan.BankLoan.lemma_A7_response
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:16:12.684443+00:00
-- url     : https://prove2.me/theorems/0d8f0366-d2cc-4c70-b26a-990f46259192
-- title:
--   Lemma A.7 parts 1–2, Appendix p. 19 (PDF 52) — the buyer insures iff $t \le t_k(w)$, otherwise borrows iff $\tau \le \tau_k(w)$
-- statement:
--   Consider the model of the mission with a regular demand law, under the paper's global assumptions ($0 < c < 1$, $l, t \ge 0$, $0 \le \tau \le \tau_0(\max(w^\alpha_2, w^E))$, $\tau < u$, $l < w^E Q^E$, $u < v$), and suppose $u + l - \tau < \hat w\hat Q$, so that the roots $w^u_1 < w^u_2$ of $u + l - \tau = w\bar F^{-1}(w)$ exist. Let $w \in (w^u_1, w^u_2)$. Then the buyer has an optimal choice (with the goodwill tie-break), and every such choice is as follows.
--
--   1. If $t \le t_k(w)$, the buyer buys insurance after borrowing and orders
--   $$Q^* = \min\Bigl(\frac{v + l - \tau - t}{w},\ \bar F^{-1}(w)\Bigr).$$
--   2. If $t > t_k(w)$, the buyer does not buy insurance; if moreover $\tau > \tau_k(w)$ it does not borrow and orders $Q^* = \min(l/w, \bar F^{-1}(w))$, and if $\tau \le \tau_k(w)$ it borrows and orders $Q^* = \min((u+l-\tau)/w, \bar F^{-1}(w))$.
--
--   This is the buyer's best response on which the supplier's pricing problem, and hence every equilibrium statement of the mission, is built.
--
--   **Formalization Note** The statement is made for $w \in (w^u_1, w^u_2)$, where the page defines $t_k$ (§4.1, "for $u + l - \tau < w\bar F^{-1}(w)$"). Existence of a response is asserted, so the statement is not vacuous. At an exact tie ($t = t_k(w)$, or $\tau = \tau_k(w)$ in case 2) the buyer is indifferent, and the goodwill rule picks the larger order only when $w > c$ (for $w < c$ it favours the smaller order, at $w = c$ it is silent); the tie cases are therefore stated for $w > c$. The page does not address prices below $c$, which the supplier never charges.
-- source:
--   Wang & Cai, Curtailing bank loan and loan insurance under risk regulations in supply chain finance, SSRN 3760840 (forthcoming Management Science 2023; PDF of 2023-02-24), Appendix p. 19 (PDF 52), Lemma A.7 parts 1–2

import Mathlib
import Definitions.Def_SupplyChainTheory_contracts
import Definitions.Def_CurtailLoan_BankLoan_Model

namespace CurtailLoan.BankLoan

/-- Lemma A.7 parts 1–2, Appendix p. 19 (PDF 52): the buyer's financing, insurance and order
decision at a price `w ∈ (w^u_1, w^u_2)`. At an exact tie (`t = tk(w)`, or `τ = τk(w)`) the
goodwill rule selects the larger order only when `c < w`, so the tie case is stated for `c < w`. -/
theorem lemma_A7_response (P : Params) (hR : P.Regular) (hG : Global P) (hD : RootsDefined P)
    (w : ℝ) (hw : w ∈ Set.Ioo (wu1 P) (wu2 P)) :
    (∃ (m : Mode) (Q : ℝ), IsResponse P w m Q) ∧
    ∀ (m : Mode) (Q : ℝ), IsResponse P w m Q →
      (P.t ≤ tk P w → (P.t < tk P w ∨ P.c < w) →
        m = Mode.insured ∧ Q = min ((P.v + P.l - P.tau - P.t) / w) (Finv P w)) ∧
      (tk P w < P.t →
        m ≠ Mode.insured ∧
        (tauk P w < P.tau → m = Mode.noLoan ∧ Q = min (P.l / w) (Finv P w)) ∧
        (P.tau ≤ tauk P w → (P.tau < tauk P w ∨ P.c < w) →
          m = Mode.loan ∧ Q = min (L P / w) (Finv P w))) := by sorry

end CurtailLoan.BankLoan

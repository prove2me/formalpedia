-- Prove2me | Theorems.Thm_CurtailLoan_BankLoan_prop2_area2_profits
-- name    : CurtailLoan.BankLoan.prop2_area2_profits
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:16:19.328918+00:00
-- url     : https://prove2.me/theorems/1d03c582-3fb0-43ee-8c71-6e4a1e86ee4a
-- title:
--   Proof of Proposition 2 (2), Appendix p. 30 (PDF 63) — equilibrium profits in Area II
-- statement:
--   Consider the model of the mission with a regular demand law under the standing assumptions and in Area II, $t_k(w_I) < t \le t_k(w_{II})$. Write $K = v + l - \tau - t$ for the insured spending cap. In every equilibrium:
--
--   1. if the insured cap binds at the equilibrium price, $K < w^t_2\bar F^{-1}(w^t_2)$, then
--   $$\Pi^{I*}_B = S\Bigl(\frac{K}{w^t_2}\Bigr) - v - l, \qquad \Pi^{I*}_S = (w^t_2 - c)\frac{K}{w^t_2};$$
--   2. if it does not bind, $w^t_2\bar F^{-1}(w^t_2) \le K$, then
--   $$\Pi^{I*}_B = S(\bar F^{-1}(w^t_2)) - w^t_2\bar F^{-1}(w^t_2) - t - \tau, \qquad \Pi^{I*}_S = (w^t_2 - c)\bar F^{-1}(w^t_2),$$
--   and $w^t_2 \le w^E$.
--
--   These closed forms reduce the comparative statics of the equilibrium profits to those of $w^t_2$.
--
--   **Formalization Note** The page prints $\Pi^{I*}_B = S(K/w^t_2) - v$ in the binding case. With the buyer's profit $S(Q) - wQ - \tau - t$ and $wQ = K$ the value is $S(K/w^t_2) - v - l$; the statement uses the model's value. The bound $w^t_2 \le w^E$ is asserted on the same page of the proof.
-- source:
--   Wang & Cai, Curtailing bank loan and loan insurance under risk regulations in supply chain finance, SSRN 3760840 (forthcoming Management Science 2023; PDF of 2023-02-24), Appendix p. 30 (PDF 63), proof of Proposition 2 (2)

import Mathlib
import Definitions.Def_SupplyChainTheory_contracts
import Definitions.Def_CurtailLoan_BankLoan_Model

namespace CurtailLoan.BankLoan

/-- Proof of Proposition 2 (2), Appendix p. 30 (PDF 63): the equilibrium profits in Area II, with
the insured cap binding or not at `w^t_2` (the page's `− v` corrected to `− v − l`). -/
theorem prop2_area2_profits (P : Params) (hR : P.Regular) (hS : Standing P) (hII : AreaII P)
    (o : Outcome) (ho : IsEquilibrium P o) :
    (P.v + P.l - P.tau - P.t < wt2 P * Finv P (wt2 P) →
      PiB P o = S P ((P.v + P.l - P.tau - P.t) / wt2 P) - P.v - P.l ∧
      PiS P o = (wt2 P - P.c) * ((P.v + P.l - P.tau - P.t) / wt2 P)) ∧
    (wt2 P * Finv P (wt2 P) ≤ P.v + P.l - P.tau - P.t →
      PiB P o = S P (Finv P (wt2 P)) - wt2 P * Finv P (wt2 P) - P.t - P.tau ∧
      PiS P o = (wt2 P - P.c) * Finv P (wt2 P) ∧
      wt2 P ≤ wE P) := by sorry

end CurtailLoan.BankLoan

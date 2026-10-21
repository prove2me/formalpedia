-- Prove2me | Theorems.Thm_CurtailLoan_BankLoan_proposition_1_1b
-- name    : CurtailLoan.BankLoan.proposition_1_1b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:16:24.137905+00:00
-- url     : https://prove2.me/theorems/b5e97e49-2e32-403f-b6dc-d6820e83fdc8
-- title:
--   Proposition 1 item 1(b), p. 12 (PDF 12) — in Area II the equilibrium price is $w^t_2$ and the buyer insures
-- statement:
--   Consider the model of the mission with a regular demand law under the standing assumptions: the buyer is capital constrained ($l < w^E Q^E$), the initial loan limit is low ($u < w^E Q^E - l + \tau$) and the insured loan limit is high ($u < v$). Suppose the fixed insurance premium is in the middle range (Area II, the insurance-cooperation region):
--   $$t_k(w_I) < t \le t_k(w_{II}).$$
--   Then an equilibrium exists, and in every equilibrium the supplier's wholesale price is $w^* = w^t_2$, the buyer buys insurance, and it orders
--   $$Q^* = \min\Bigl(\frac{v + l - \tau - t}{w^t_2},\ \bar F^{-1}(w^t_2)\Bigr).$$
--
--   In this region the supplier cuts its price below what it would charge without insurance just far enough that the buyer is willing to pay the premium: this is the cooperation on which the mission's goal rests.
--
--   **Formalization Note** Equilibria use the paper's goodwill tie-breaking rule in both stages; at $w^t_2$ the buyer is exactly indifferent about insuring, so without the buyer's goodwill no equilibrium would exist. Existence is part of the statement.
-- source:
--   Wang & Cai, Curtailing bank loan and loan insurance under risk regulations in supply chain finance, SSRN 3760840 (forthcoming Management Science 2023; PDF of 2023-02-24), pp. 11–12 (PDF 11–12), Proposition 1 item 1(b); restated as Proposition A.8 1(b), Appendix pp. 22–23 (PDF 55–56)

import Mathlib
import Definitions.Def_SupplyChainTheory_contracts
import Definitions.Def_CurtailLoan_BankLoan_Model

namespace CurtailLoan.BankLoan

/-- Proposition 1 item 1(b), p. 12 (PDF 12): in Area II an equilibrium exists, and every
equilibrium has `w* = w^t_2`, an insured loan, and `Q* = min((v+l−τ−t)/w^t_2, F̄^{-1}(w^t_2))`. -/
theorem proposition_1_1b (P : Params) (hR : P.Regular) (hS : Standing P) (hII : AreaII P) :
    (∃ o : Outcome, IsEquilibrium P o) ∧
    ∀ o : Outcome, IsEquilibrium P o →
      o.w = wt2 P ∧ o.m = Mode.insured ∧
      o.Q = min ((P.v + P.l - P.tau - P.t) / wt2 P) (Finv P (wt2 P)) := by sorry

end CurtailLoan.BankLoan

-- Prove2me | Theorems.Thm_FinancialDerivatives_FD03_localHedge_cost
-- name    : FinancialDerivatives.FD03.localHedge_cost
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T07:59:53.246062+00:00
-- url     : https://prove2.me/theorems/c63fff53-7828-45ad-a06a-475876b05f53
-- title:
--   Replicating hedge cost equals risk-neutral node price
-- statement:
--   The current value ΔS+b of a local hedge that produces the specified up/down payments equals their discounted market-implied one-step risk-neutral value.
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapter 10 §§10.2–10.4, printed pp. 182–189. Derived two-state replication valuation identity.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_localHedge
import Definitions.Def_fd03_oneStepValue

namespace FinancialDerivatives.FD03

theorem localHedge_cost (m : BinomialMarket) (spot vu vd : ℝ)
    (hspot : 0 < spot) :
    (localHedge m spot vu vd).1 * spot +
      (localHedge m spot vu vd).2 = oneStepValue m vu vd := by sorry

end FinancialDerivatives.FD03

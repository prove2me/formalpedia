-- Prove2me | Theorems.Thm_FinancialDerivatives_FD03_localHedge_down
-- name    : FinancialDerivatives.FD03.localHedge_down
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T07:59:43.878528+00:00
-- url     : https://prove2.me/theorems/6cd71b2c-ad99-45c9-b9fd-8aa75cef85a9
-- title:
--   Local binomial hedge replicates the down-state payment
-- statement:
--   At a strictly positive node stock price, the explicitly defined local stock-and-bank holdings pay exactly Vₔ after the down move and one period of bank growth.
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapter 10 §§10.2–10.4, printed pp. 182–189. Derived one-step hedge replication.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_localHedge

namespace FinancialDerivatives.FD03

theorem localHedge_down (m : BinomialMarket) (spot vu vd : ℝ)
    (hspot : 0 < spot) :
    (localHedge m spot vu vd).1 * (spot * m.down) +
      (localHedge m spot vu vd).2 * m.growth = vd := by sorry

end FinancialDerivatives.FD03

-- Prove2me | Theorems.Thm_FinancialDerivatives_FD02_riskNeutral_stock_martingale
-- name    : FinancialDerivatives.FD02.riskNeutral_stock_martingale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T00:06:26.381009+00:00
-- url     : https://prove2.me/theorems/c6ed82d5-cc06-458e-abe4-a1bb0959cc62
-- title:
--   Risk-neutral stock growth equals bank growth
-- statement:
--   The candidate risk-neutral probability is calibrated so the expected stock gross return equals the bank accumulation factor.
--
--   This is an original derived theorem target; a remote compiler must validate its declaration and proof.
-- source:
--   Derived from Wilmott, Howison and Dewynne (1995), §10.2, equation (10.4), p. 183. https://doi.org/10.1017/CBO9780511812545.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd02_TwoStateMarket
import Definitions.Def_fd02_riskNeutralUp

namespace FinancialDerivatives.FD02

/-- Risk-neutral stock growth equals bank growth. -/
theorem riskNeutral_stock_martingale (m : TwoStateMarket) :
  riskNeutralUp m * m.up + (1 - riskNeutralUp m) * m.down = m.growth := by sorry

end FinancialDerivatives.FD02

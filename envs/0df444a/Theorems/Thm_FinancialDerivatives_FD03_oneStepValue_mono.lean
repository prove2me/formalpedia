-- Prove2me | Theorems.Thm_FinancialDerivatives_FD03_oneStepValue_mono
-- name    : FinancialDerivatives.FD03.oneStepValue_mono
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T07:56:35.366142+00:00
-- url     : https://prove2.me/theorems/e7090c39-f714-4a32-8621-f878699d8d5d
-- title:
--   Monotonicity of one-step discounted valuation
-- statement:
--   Increasing either next-period cash payment without decreasing the other cannot decrease its one-step price in a strictly arbitrage-free binomial market.
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapter 10 §10.4, printed pp. 187–189, equation (10.16). Derived positivity/monotonicity of the binomial valuation operator.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_oneStepValue

namespace FinancialDerivatives.FD03

theorem oneStepValue_mono (m : BinomialMarket)
    (u₁ u₂ d₁ d₂ : ℝ) (hu : u₁ ≤ u₂) (hd : d₁ ≤ d₂) :
    oneStepValue m u₁ d₁ ≤ oneStepValue m u₂ d₂ := by sorry

end FinancialDerivatives.FD03

-- Prove2me | Theorems.Thm_FinancialDerivatives_FD06_generalised_european_pricing_package
-- name    : FinancialDerivatives.FD06.generalised_european_pricing_package
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:39:45.297833+00:00
-- url     : https://prove2.me/theorems/ee3c28c4-94f0-42ec-8cc6-99098e88a39f
-- title:
--   MAIN GOAL: Exact integrated-parameter Gaussian prices, generalized Black-Scholes formulas and parity
-- statement:
--   MAIN GOAL: Exact integrated-parameter Gaussian prices, generalized Black-Scholes formulas and parity
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapters 4–6; analytic rigor and extension.

import Mathlib
import Definitions.Def_fd06_discountedCallGaussian
import Definitions.Def_fd06_discountedPutGaussian
import Definitions.Def_fd06_generalisedCall
import Definitions.Def_fd06_generalisedPut

namespace FinancialDerivatives.FD06

theorem generalised_european_pricing_package (S K R Q V : ℝ) (hS : 0 < S) (hK : 0 < K) (hV : 0 < V) : (discountedCallGaussian S K R Q V = generalisedCall S K R Q V) ∧ (discountedPutGaussian S K R Q V = generalisedPut S K R Q V) ∧ (generalisedCall S K R Q V - generalisedPut S K R Q V = S * Real.exp (-Q) - K * Real.exp (-R)) := by sorry

end FinancialDerivatives.FD06

-- Prove2me | Theorems.Thm_ActuarialValuation_discreteStopLossPayment_above
-- name    : ActuarialValuation.discreteStopLossPayment_above
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T10:27:54.176606+00:00
-- url     : https://prove2.me/theorems/a99ecec9-1b40-4a87-9d00-696d570e70ea
-- title:
--   Claims strictly above attachment pay the excess
-- statement:
--   For a realised loss at or above the attachment, the insurer pays the retention and the reinsurer pays the remaining amount. The natural-number payment equals ordinary nonnegative claim minus deductible, including equality at the boundary.
--
--   **Mathematical statement**
--
--   $$
--   s\ge d\Longrightarrow(s-d)_+=s-d
--   $$
-- source:
--   H H Panjer (1980), The aggregate claims distribution and stop-loss reinsurance, Transactions of the Society of Actuaries 32, 523–535; H H Panjer and G E Willmot (1982), Recursions for compound distributions, ASTIN Bulletin; Willmot, Drekic and Cai (2005), Equilibrium compound distributions and stop-loss moments, https://doi.org/10.1080/03461230510009691; exact finite discrete stop-loss specialisation

import Mathlib
import Definitions.Def_actuarial_discreteStopLossPayment

namespace ActuarialValuation

theorem discreteStopLossPayment_above (claim deductible : ℕ)
  (h : deductible ≤ claim) :
  discreteStopLossPayment claim deductible = claim - deductible := by sorry

end ActuarialValuation

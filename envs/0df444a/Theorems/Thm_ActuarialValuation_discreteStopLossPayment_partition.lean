-- Prove2me | Theorems.Thm_ActuarialValuation_discreteStopLossPayment_partition
-- name    : ActuarialValuation.discreteStopLossPayment_partition
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T10:32:17.760351+00:00
-- url     : https://prove2.me/theorems/04fd813d-4e52-4a02-b036-07480038c7a6
-- title:
--   Retained claim and ceded stop-loss payment sum to gross loss
-- statement:
--   Every realised integer aggregate claim is divided into a retained amount capped at the attachment and an excess amount paid by the reinsurer. This pathwise conservation is valid on both sides of the deductible and at exact equality.
--
--   **Mathematical statement**
--
--   $$
--   \min(s,d)+(s-d)_+=s
--   $$
-- source:
--   H H Panjer (1980), The aggregate claims distribution and stop-loss reinsurance, Transactions of the Society of Actuaries 32, 523–535; H H Panjer and G E Willmot (1982), Recursions for compound distributions, ASTIN Bulletin; Willmot, Drekic and Cai (2005), Equilibrium compound distributions and stop-loss moments, https://doi.org/10.1080/03461230510009691; exact finite discrete stop-loss specialisation

import Mathlib
import Definitions.Def_actuarial_discreteStopLossPayment

namespace ActuarialValuation

theorem discreteStopLossPayment_partition (claim deductible : ℕ) :
  min claim deductible + discreteStopLossPayment claim deductible = claim := by sorry

end ActuarialValuation

-- Prove2me | Theorems.Thm_ActuarialValuation_irIndex_at_zero
-- name    : ActuarialValuation.irIndex_at_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T19:00:58.494501+00:00
-- url     : https://prove2.me/theorems/40d3a05c-cf57-464e-a8cb-6dfa256728b0
-- title:
--   Inflation indices and real-claims transformations: irIndex_at_zero
-- statement:
--   Zero inflation keeps the original claims cost index. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   C^{\text{real}}_{i,j}=C_{i,j}\frac{I_{\text{base}}}{I_{i+j}}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 382. Institute and Faculty of Actuaries, High-level Methods for Incorporating Changing Inflation into Claims Reserve Estimates, https://vle.actuaries.org.uk/pluginfile.php/168696/mod_resource/content/1/Reserving%20During%20Volatile%20Inflation%20v1.9.pdf; IFoA Claims Reserving report, https://www.actuaries.org.uk/system/files/documents/pdf/0353-0413.pdf. Parent topic: Inflation-adjusted incremental triangle with calendar-year indices, de-inflation, development and reinflation; claim-frequency and average-cost ultimate reserve reconciliation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuaries.org.uk/system/files/documents/pdf/0353-0413.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_irPriceIndex

namespace ActuarialValuation

theorem irIndex_at_zero (base : ℝ) : irPriceIndex base 0=base := by sorry

end ActuarialValuation

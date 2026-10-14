-- Prove2me | Theorems.Thm_ActuarialValuation_irDeflate_equal_index
-- name    : ActuarialValuation.irDeflate_equal_index
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T19:01:09.748595+00:00
-- url     : https://prove2.me/theorems/238f1e44-3bfd-47e1-9c11-c80aff951d55
-- title:
--   Inflation indices and real-claims transformations: irDeflate_equal_index
-- statement:
--   Historic claims need no adjustment when already at base-year prices. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_irDeflate

namespace ActuarialValuation

theorem irDeflate_equal_index (claim index : ℝ) (hi : index≠0) : irDeflate claim index index=claim := by sorry

end ActuarialValuation

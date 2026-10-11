-- Prove2me | Theorems.Thm_ActuarialValuation_irDeflate_add
-- name    : ActuarialValuation.irDeflate_add
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T19:02:35.744234+00:00
-- url     : https://prove2.me/theorems/88093759-2633-4813-bda4-1ef9ad3fe8d5
-- title:
--   Inflation indices and real-claims transformations: irDeflate_add
-- statement:
--   Inflation-adjusted payments remain additive within one calendar year. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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

theorem irDeflate_add (a b base hist : ℝ) : irDeflate (a+b) base hist=irDeflate a base hist+irDeflate b base hist := by sorry

end ActuarialValuation

-- Prove2me | Theorems.Thm_ActuarialValuation_irReinflate_nonneg
-- name    : ActuarialValuation.irReinflate_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T19:02:24.745052+00:00
-- url     : https://prove2.me/theorems/7e822cfc-b263-44c9-a5bf-f6a5f5aeb12d
-- title:
--   Inflation indices and real-claims transformations: irReinflate_nonneg
-- statement:
--   Positive base indices preserve nonnegative nominal claim payments. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_irReinflate

namespace ActuarialValuation

theorem irReinflate_nonneg (claim future base : ℝ) (hc : 0≤claim) (hf : 0≤future) (hb : 0<base) : 0≤irReinflate claim future base := by sorry

end ActuarialValuation

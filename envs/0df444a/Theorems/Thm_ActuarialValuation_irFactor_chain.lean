-- Prove2me | Theorems.Thm_ActuarialValuation_irFactor_chain
-- name    : ActuarialValuation.irFactor_chain
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T19:03:02.735+00:00
-- url     : https://prove2.me/theorems/6639b7eb-7835-44f8-b418-07ef8b729c55
-- title:
--   Inflation indices and real-claims transformations: irFactor_chain
-- statement:
--   Calendar-year inflation ratios compose without arbitrage-like price drift. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_irFactor

namespace ActuarialValuation

theorem irFactor_chain (a b c : ℝ) (ha : a≠0) (hb : b≠0) : irFactor c b*irFactor b a=irFactor c a := by sorry

end ActuarialValuation

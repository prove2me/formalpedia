-- Prove2me | Theorems.Thm_ActuarialValuation_irRealReserve_balance
-- name    : ActuarialValuation.irRealReserve_balance
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T19:05:54.262255+00:00
-- url     : https://prove2.me/theorems/09ff227c-7fef-4de0-b271-9b98baeb6d45
-- title:
--   Incremental triangles and cumulative development: irRealReserve_balance
-- statement:
--   Real outstanding claims reconcile with projected ultimate claims. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   C_{i,j}=\sum_{k=0}^{j}X_{i,k},\quad U_i=C_{i,j}f_j
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 382. Institute and Faculty of Actuaries, High-level Methods for Incorporating Changing Inflation into Claims Reserve Estimates, https://vle.actuaries.org.uk/pluginfile.php/168696/mod_resource/content/1/Reserving%20During%20Volatile%20Inflation%20v1.9.pdf; IFoA Claims Reserving report, https://www.actuaries.org.uk/system/files/documents/pdf/0353-0413.pdf. Parent topic: Inflation-adjusted incremental triangle with calendar-year indices, de-inflation, development and reinflation; claim-frequency and average-cost ultimate reserve reconciliation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuaries.org.uk/system/files/documents/pdf/0353-0413.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_irRealReserve

namespace ActuarialValuation

theorem irRealReserve_balance (ultimate paid : ℝ) : irRealReserve ultimate paid+paid=ultimate := by sorry

end ActuarialValuation

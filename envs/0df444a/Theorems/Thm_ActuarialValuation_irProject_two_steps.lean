-- Prove2me | Theorems.Thm_ActuarialValuation_irProject_two_steps
-- name    : ActuarialValuation.irProject_two_steps
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T19:05:28.080975+00:00
-- url     : https://prove2.me/theorems/95ffb850-347d-4e7d-aefb-c6e83b2a9050
-- title:
--   Incremental triangles and cumulative development: irProject_two_steps
-- statement:
--   Successive development factors reproduce a factor-to-ultimate. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_irProject

namespace ActuarialValuation

theorem irProject_two_steps (paid f g : ℝ) : irProject (irProject paid f) g=irProject paid (f*g) := by sorry

end ActuarialValuation

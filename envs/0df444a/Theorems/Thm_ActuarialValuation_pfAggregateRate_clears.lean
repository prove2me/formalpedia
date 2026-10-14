-- Prove2me | Theorems.Thm_ActuarialValuation_pfAggregateRate_clears
-- name    : ActuarialValuation.pfAggregateRate_clears
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T18:02:18.072144+00:00
-- url     : https://prove2.me/theorems/12489663-4d44-4c41-8fa3-bc2274bfb12a
-- title:
--   Aggregate funding and deficit amortisation: pfAggregateRate_clears
-- statement:
--   Aggregate funding rate finances projected benefits after existing assets. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   r_{\text{agg}}=\frac{B_x-A_x}{P_x},\qquad r_{\text{modified}}=r_{\text{normal}}+\frac{L_x-A_x}{a}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 7. Institute and Faculty of Actuaries, GN26 Pension Fund Terminology, §§4.5–4.9, https://www.actuaries.org.uk/system/files/documents/pdf/gn26v2-0.pdf; OECD Working Paper, Funding Rules and Actuarial Methods, §§74–76, https://www.oecd.org/content/dam/oecd/en/publications/reports/2006/10/funding-rules-and-actuarial-methods_g17a1941/274307371724.pdf; Actuarial Standards Board ASOP No.4, https://www.actuarialstandardsboard.org/asops/measuring-pension-obligations-determining-pension-plan-costs-contributions/. Parent topic: Entry age and attained age normal costs, aggregate and modified contributions, deficit amortisation and exact funding-surplus rollforward. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuaries.org.uk/system/files/documents/pdf/gn26v2-0.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pfAggregateRate

namespace ActuarialValuation

theorem pfAggregateRate_clears (benefit assets payroll : ℝ) (hp : payroll≠0) : assets+pfAggregateRate benefit assets payroll*payroll=benefit := by sorry

end ActuarialValuation

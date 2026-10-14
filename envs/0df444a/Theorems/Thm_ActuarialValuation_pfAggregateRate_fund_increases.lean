-- Prove2me | Theorems.Thm_ActuarialValuation_pfAggregateRate_fund_increases
-- name    : ActuarialValuation.pfAggregateRate_fund_increases
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T18:02:51.694005+00:00
-- url     : https://prove2.me/theorems/408c102c-565e-4dad-bd42-123f37d41044
-- title:
--   Aggregate funding and deficit amortisation: pfAggregateRate_fund_increases
-- statement:
--   More fund assets reduce aggregate normal cost. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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

theorem pfAggregateRate_fund_increases (benefit asset1 asset2 payroll : ℝ) (h : asset1≤asset2) (hp : 0<payroll) : pfAggregateRate benefit asset2 payroll≤pfAggregateRate benefit asset1 payroll := by sorry

end ActuarialValuation

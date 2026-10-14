-- Prove2me | Theorems.Thm_ActuarialValuation_pfAttainedRate_zero_future
-- name    : ActuarialValuation.pfAttainedRate_zero_future
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T18:01:31.15646+00:00
-- url     : https://prove2.me/theorems/75835203-ee75-4d85-852a-f297a423f55a
-- title:
--   Entry age, attained age and liability allocation: pfAttainedRate_zero_future
-- statement:
--   If all projected benefits are accrued there are no future-service normal costs. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   r_{\text{entry}}=\frac{B_e}{P_e},\qquad L_x=B_x-r_{\text{entry}}P_x
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 7. Institute and Faculty of Actuaries, GN26 Pension Fund Terminology, §§4.5–4.9, https://www.actuaries.org.uk/system/files/documents/pdf/gn26v2-0.pdf; OECD Working Paper, Funding Rules and Actuarial Methods, §§74–76, https://www.oecd.org/content/dam/oecd/en/publications/reports/2006/10/funding-rules-and-actuarial-methods_g17a1941/274307371724.pdf; Actuarial Standards Board ASOP No.4, https://www.actuarialstandardsboard.org/asops/measuring-pension-obligations-determining-pension-plan-costs-contributions/. Parent topic: Entry age and attained age normal costs, aggregate and modified contributions, deficit amortisation and exact funding-surplus rollforward. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuaries.org.uk/system/files/documents/pdf/gn26v2-0.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pfAttainedRate

namespace ActuarialValuation

theorem pfAttainedRate_zero_future (past payroll : ℝ) : pfAttainedRate past past payroll=0 := by sorry

end ActuarialValuation

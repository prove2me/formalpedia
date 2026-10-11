-- Prove2me | Theorems.Thm_ActuarialValuation_pfAttainedCost_relation
-- name    : ActuarialValuation.pfAttainedCost_relation
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T18:02:06.06032+00:00
-- url     : https://prove2.me/theorems/35f4eae7-1651-4861-81b9-1eee38b72736
-- title:
--   Entry age, attained age and liability allocation: pfAttainedCost_relation
-- statement:
--   Annual attained normal cost equals rate times current pensionable earnings. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_pfAttainedNormalCost

namespace ActuarialValuation

theorem pfAttainedCost_relation (total past payroll pay : ℝ) : pfAttainedNormalCost total past payroll pay=pfAttainedRate total past payroll*pay := by sorry

end ActuarialValuation

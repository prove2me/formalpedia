-- Prove2me | Theorems.Thm_ActuarialValuation_pfLiabilitiesNext_assumption_shift
-- name    : ActuarialValuation.pfLiabilitiesNext_assumption_shift
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T18:06:31.918169+00:00
-- url     : https://prove2.me/theorems/a6368f39-dcff-4962-a792-b4837c259c10
-- title:
--   Fund asset rollforward and exact surplus attribution: pfLiabilitiesNext_assumption_shift
-- statement:
--   A positive basis-change effect increases the closing liability. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   S_{t+1}-S_t=(A_{t+1}-A_t)-(L_{t+1}-L_t)
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 7. Institute and Faculty of Actuaries, GN26 Pension Fund Terminology, §§4.5–4.9, https://www.actuaries.org.uk/system/files/documents/pdf/gn26v2-0.pdf; OECD Working Paper, Funding Rules and Actuarial Methods, §§74–76, https://www.oecd.org/content/dam/oecd/en/publications/reports/2006/10/funding-rules-and-actuarial-methods_g17a1941/274307371724.pdf; Actuarial Standards Board ASOP No.4, https://www.actuarialstandardsboard.org/asops/measuring-pension-obligations-determining-pension-plan-costs-contributions/. Parent topic: Entry age and attained age normal costs, aggregate and modified contributions, deficit amortisation and exact funding-surplus rollforward. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuaries.org.uk/system/files/documents/pdf/gn26v2-0.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pfLiabilitiesNext

namespace ActuarialValuation

theorem pfLiabilitiesNext_assumption_shift (liability s i b experience extra : ℝ) : pfLiabilitiesNext liability s i b (experience+extra)=pfLiabilitiesNext liability s i b experience+extra := by sorry

end ActuarialValuation

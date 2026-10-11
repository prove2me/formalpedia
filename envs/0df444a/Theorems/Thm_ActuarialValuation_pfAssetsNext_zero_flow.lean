-- Prove2me | Theorems.Thm_ActuarialValuation_pfAssetsNext_zero_flow
-- name    : ActuarialValuation.pfAssetsNext_zero_flow
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T18:05:32.377462+00:00
-- url     : https://prove2.me/theorems/88c2c09e-a485-40b4-ba13-146bf6cbe998
-- title:
--   Fund asset rollforward and exact surplus attribution: pfAssetsNext_zero_flow
-- statement:
--   An unchanged fund remains at its initial asset value. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_pfAssetsNext

namespace ActuarialValuation

theorem pfAssetsNext_zero_flow (a : ℝ) : pfAssetsNext a 0 0 0 0=a := by sorry

end ActuarialValuation

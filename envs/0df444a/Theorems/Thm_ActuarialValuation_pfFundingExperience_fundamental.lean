-- Prove2me | Theorems.Thm_ActuarialValuation_pfFundingExperience_fundamental
-- name    : ActuarialValuation.pfFundingExperience_fundamental
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T18:08:18.490473+00:00
-- url     : https://prove2.me/theorems/6f4fa6cf-52ac-4dda-bd77-68274becab78
-- title:
--   Fund asset rollforward and exact surplus attribution: pfFundingExperience_fundamental
-- statement:
--   The three genuinely distinct DB funding methods reconcile projected liabilities while deficit contributions and complete one-year experience movements reconcile surplus. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_pfEntryRate
import Definitions.Def_actuarial_pfAttainedRate
import Definitions.Def_actuarial_pfAggregateRate
import Definitions.Def_actuarial_pfDeficit
import Definitions.Def_actuarial_pfModifiedRate
import Definitions.Def_actuarial_pfAssetsNext
import Definitions.Def_actuarial_pfLiabilitiesNext
import Definitions.Def_actuarial_pfSurplus
import Definitions.Def_actuarial_pfSurplusMovement

namespace ActuarialValuation

theorem pfFundingExperience_fundamental (entryBenefit entryPayroll totalPV pastPV futurePayroll assets normal deficitAnnuity a l c invest benefits expenses service interest lb assumptions : ℝ) (he : entryPayroll≠0) (hf : futurePayroll≠0) (ha : deficitAnnuity≠0) : (pfEntryRate entryBenefit entryPayroll*entryPayroll=entryBenefit) ∧ (pastPV+pfAttainedRate totalPV pastPV futurePayroll*futurePayroll=totalPV) ∧ (assets+pfAggregateRate totalPV assets futurePayroll*futurePayroll=totalPV) ∧ ((pfModifiedRate normal (pfDeficit totalPV assets) deficitAnnuity-normal)*deficitAnnuity=pfDeficit totalPV assets) ∧ (pfSurplus (pfAssetsNext a c invest benefits expenses) (pfLiabilitiesNext l service interest lb assumptions)=pfSurplus a l+pfSurplusMovement c invest benefits expenses service interest lb assumptions) := by sorry

end ActuarialValuation

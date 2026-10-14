-- Prove2me | Theorems.Thm_ActuarialValuation_irCombinedReserving_fundamental
-- name    : ActuarialValuation.irCombinedReserving_fundamental
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T19:08:50.320264+00:00
-- url     : https://prove2.me/theorems/615428d8-338f-404e-a638-b9cb223420fd
-- title:
--   Average-cost-per-claim projection and reserve reconciliation: irCombinedReserving_fundamental
-- statement:
--   The inflation-adjusted chain-ladder projection and the independently developed average-cost claim reserve both reconcile nominal cashflows, real development and ultimate claims without treating the projection as an observed fact. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   U_i=N_i^{\text{ult}}A_i^{\text{ult}},\quad R_i=U_i-P_i
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 382. Institute and Faculty of Actuaries, High-level Methods for Incorporating Changing Inflation into Claims Reserve Estimates, https://vle.actuaries.org.uk/pluginfile.php/168696/mod_resource/content/1/Reserving%20During%20Volatile%20Inflation%20v1.9.pdf; IFoA Claims Reserving report, https://www.actuaries.org.uk/system/files/documents/pdf/0353-0413.pdf. Parent topic: Inflation-adjusted incremental triangle with calendar-year indices, de-inflation, development and reinflation; claim-frequency and average-cost ultimate reserve reconciliation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuaries.org.uk/system/files/documents/pdf/0353-0413.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_irDeflate
import Definitions.Def_actuarial_irReinflate
import Definitions.Def_actuarial_irProject
import Definitions.Def_actuarial_irRealReserve
import Definitions.Def_actuarial_irClaimCountUltimate
import Definitions.Def_actuarial_irClaimCostUltimate
import Definitions.Def_actuarial_irACPCUltimate
import Definitions.Def_actuarial_irACPCReserve

namespace ActuarialValuation

theorem irCombinedReserving_fundamental (historic base old future paid realLatest link count countFactor avg costFactor : ℝ) (hbase : base≠0) (hold : old≠0) (hfuture : future≠0) : (irReinflate (irDeflate historic base old) old base=historic) ∧ (irProject realLatest link-realLatest=irRealReserve (irProject realLatest link) realLatest) ∧ (irACPCReserve (irClaimCountUltimate count countFactor) (irClaimCostUltimate avg costFactor) paid+paid=irACPCUltimate count avg*(countFactor*costFactor)) := by sorry

end ActuarialValuation

-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_RF_reprod
-- name    : CompanionTheory.D.gk.RF.reprod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:35:25.357826+00:00
-- url     : https://prove2.me/theorems/78abd97f-0fee-4a05-b987-8867c2a1070d
-- title:
--   RF: reprod
-- statement:
--   The RF construction uses the reprod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/FundamentalDomainCusps/IntegrableMulBc.lean#L66-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/FundamentalDomainCusps/IntegrableMulBc.lean#L66-L69

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_CompactIntegralBoundedByQuotientNorm
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CapelliComplements_FirstLemmaL
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_IntegrableMulBc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Filter BoundedContinuousFunction
open scoped ENNReal
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.RF
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]

theorem CompanionTheory.D.gk.RF.reprod {φ : G → ℂ} (hφ : Integrable φ μ) (hi : ∀ w, ∫ y, φ y * φ (y⁻¹ * w) ∂μ = φ w) {F : G → ℂ}
    (hF : Continuous F) {M : ℝ} (hM : ∀ y, ‖F y‖ ≤ M) :
    ∫ y, φ y * ∫ z, φ z * F (y * z) ∂μ ∂μ = ∫ w, φ w * F w ∂μ := by sorry

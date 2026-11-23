-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_RF_integrable_mul_bc
-- name    : CompanionTheory.D.gk.RF.integrable_mul_bc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:35:21.413725+00:00
-- url     : https://prove2.me/theorems/77910746-fac9-425c-b7c1-8b70dcc1bb78
-- title:
--   RF: integrable mul bc
-- statement:
--   The RF construction uses the integrable mul bc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/FundamentalDomainCusps/IntegrableMulBc.lean#L62-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/FundamentalDomainCusps/IntegrableMulBc.lean#L62-L64

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

theorem CompanionTheory.D.gk.RF.integrable_mul_bc {φ : G → ℂ} (hφ : Integrable φ μ) {F : G → ℂ} (hF : Continuous F) {M : ℝ}
    (hM : ∀ y, ‖F y‖ ≤ M) : Integrable (fun y => φ y * F y) μ := by sorry

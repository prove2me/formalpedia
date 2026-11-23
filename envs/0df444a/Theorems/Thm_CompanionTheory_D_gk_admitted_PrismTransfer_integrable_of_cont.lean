-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_PrismTransfer_integrable_of_cont
-- name    : CompanionTheory.D.gk.admitted.PrismTransfer.integrable_of_cont
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:26:13.586893+00:00
-- url     : https://prove2.me/theorems/ba2d8355-47ac-49d6-b45b-ad05834e0110
-- title:
--   Prism Transfer: integrable of cont
-- statement:
--   The Prism Transfer construction uses the integrable of cont property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/Transfer.lean#L193-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/Transfer.lean#L193-L195

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_Transfer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped Kronecker Pointwise
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted
open CompanionTheory.D.gk.admitted.PrismTransfer
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {K : Subgroup G} [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ]
  (e : K → ℂ)
variable {μ e}
omit [IsTopologicalGroup G]

theorem CompanionTheory.D.gk.admitted.PrismTransfer.integrable_of_cont {V : Type} [NormedAddCommGroup V] [SecondCountableTopology K] {f : K → V}
    (hf : Continuous f) : Integrable f μ := by sorry

-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_PrismTransfer_IsFam_sub
-- name    : CompanionTheory.D.gk.admitted.PrismTransfer.IsFam.sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:31:22.945014+00:00
-- url     : https://prove2.me/theorems/df67225b-f3e5-4b65-b83f-18c88ef57ccd
-- title:
--   Is Fam: sub
-- statement:
--   The Is Fam construction uses the sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/Transfer.lean#L197-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/Transfer.lean#L197-L211

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

theorem CompanionTheory.D.gk.admitted.PrismTransfer.IsFam.sub [SecondCountableTopology K] (he : Continuous e) {Φ Φ' : G → ℂ} {F F' : List G → G → ℂ}
    (h : IsFam μ e Φ F) (h' : IsFam μ e Φ' F') :
    IsFam μ e (fun x => Φ x - Φ' x) (fun l x => F l x - F' l x) := by sorry

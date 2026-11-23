-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_PrismTransfer_isFam_rep
-- name    : CompanionTheory.D.gk.admitted.PrismTransfer.isFam_rep
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:31:44.043882+00:00
-- url     : https://prove2.me/theorems/e1d35922-2d26-410c-b525-6a8ff34a48cb
-- title:
--   Prism Transfer: is Fam rep
-- statement:
--   The Prism Transfer construction uses the is Fam rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/Transfer.lean#L239-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/Transfer.lean#L239-L255

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

theorem CompanionTheory.D.gk.admitted.PrismTransfer.isFam_rep [SecondCountableTopology K] (he : Continuous e) {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [CompleteSpace V] (τ : G →* Module.End ℂ V) (h1 : ∀ x, Continuous (τ x))
    (h2 : ∀ v, Continuous fun x => τ x v) (E : Module.End ℂ V) (hE : ∀ u, E u = ∫ k : K, e k • τ k u ∂μ)
    (ℓ : V →L[ℂ] ℂ) (u : V) :
    IsFam μ e (fun x => ℓ (τ x u)) (fun l x => ℓ (τ x (word E (l.map τ) u))) := by sorry

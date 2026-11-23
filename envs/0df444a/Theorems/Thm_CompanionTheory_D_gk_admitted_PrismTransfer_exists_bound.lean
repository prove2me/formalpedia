-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_PrismTransfer_exists_bound
-- name    : CompanionTheory.D.gk.admitted.PrismTransfer.exists_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:31:35.865249+00:00
-- url     : https://prove2.me/theorems/30c47bea-dc78-43b5-b983-91415e4f8251
-- title:
--   Prism Transfer: exists bound
-- statement:
--   The Prism Transfer construction uses the exists bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/Transfer.lean#L221-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/Transfer.lean#L221-L236

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

theorem CompanionTheory.D.gk.admitted.PrismTransfer.exists_bound [SecondCountableTopology K] (he : Continuous e) (l : List G) :
    ∀ C : Set G, IsCompact C → ∃ C' : Set G, IsCompact C' ∧ ∀ Φ F, IsFam μ e Φ F → ∀ δ : ℝ,
      (∀ y ∈ C', ‖Φ y‖ ≤ δ) → ∀ x ∈ C, ‖F l x‖ ≤ (∫ k, ‖e k‖ ∂μ) ^ (l.length + 1) * δ := by sorry

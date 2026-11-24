-- Prove2me | Theorems.Thm_EisTube_psi_cont
-- name    : EisTube.psi_cont
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:21:41.412908+00:00
-- url     : https://prove2.me/theorems/71676e1d-69fe-4a79-9691-e02e66bb6aa2
-- title:
--   Eis Tube: psi cont
-- statement:
--   The Eis Tube construction uses the psi cont property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/EisensteinSeriesG2/TubeDomainExtension/TubeExtendsFarCone.lean#L241-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/EisensteinSeriesG2/TubeDomainExtension/TubeExtendsFarCone.lean#L241-L268

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_TubeDomainExtension_Statement
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_TubeDomainExtension_Lemmas
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_TubeDomainExtension_TubeExtendsFarCone
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology MeasureTheory
open EisTube
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
variable {ι : Type} [Fintype ι]
variable {P : Type*} [TopologicalSpace P]

theorem EisTube.psi_cont [FirstCountableTopology P] {Ω : Set (ι → ℝ)} {h : P → ℝ} (h0 : ∀ p, 0 ≤ h p)
    (hloc : ∀ p, ∃ U ∈ 𝓝 p, BddAbove (h '' U)) {F : (ι → ℂ) → P → ℂ}
    (hhol : ∀ p, DifferentiableOn ℂ (fun z => F z p) (tube Ω))
    (hcont : ∀ z ∈ tube Ω, Continuous (F z))
    (hbd : ∀ K ⊆ Ω, IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ z : ι → ℂ, reV z ∈ K → ∀ p,
      ‖F z p‖ ≤ C * h p * (1 + ‖imV z‖) ^ N)
    {x₀ : ι → ℝ} (h₀ : x₀ ∈ Ω) (t : ι → ℝ) :
    Continuous (fun p => psiAt F x₀ p t) := by sorry

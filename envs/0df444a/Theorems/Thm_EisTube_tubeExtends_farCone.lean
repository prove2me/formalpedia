-- Prove2me | Theorems.Thm_EisTube_tubeExtends_farCone
-- name    : EisTube.tubeExtends_farCone
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:18:07.732817+00:00
-- url     : https://prove2.me/theorems/079ca1b5-ec32-5880-b87f-2eb96c323a96
-- title:
--   Eis Tube: tube Extends far Cone
-- statement:
--   The Eis Tube construction uses the tube Extends far Cone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/EisensteinSeriesG2/TubeDomainExtension/TubeExtendsFarCone.lean#L335-L382
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/EisensteinSeriesG2/TubeDomainExtension/TubeExtendsFarCone.lean#L335-L382

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

theorem EisTube.tubeExtends_farCone {J : Type*} [Fintype J]
    (P : Type*) [TopologicalSpace P] [FirstCountableTopology P]
    (a : J → ι → ℝ) (R : ℝ) (hR : 0 ≤ R) (hne : (farCone a R).Nonempty)
    (Ω : Set (ι → ℝ)) (hΩo : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hpos : farCone a R ⊆ Ω) (hneg : ∀ x ∈ farCone a R, -x ∈ Ω)
    (h : P → ℝ) (h0 : ∀ p, 0 ≤ h p) (hloc : ∀ p, ∃ U ∈ 𝓝 p, BddAbove (h '' U))
    (F : (ι → ℂ) → P → ℂ)
    (hhol : ∀ p, DifferentiableOn ℂ (fun z => F z p) (tube Ω))
    (hcont : ∀ z ∈ tube Ω, Continuous (F z))
    (hbd : ∀ K ⊆ Ω, IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ z : ι → ℂ, reV z ∈ K → ∀ p,
      ‖F z p‖ ≤ C * h p * (1 + ‖imV z‖) ^ N) :
    ∃ G : (ι → ℂ) → P → ℂ,
      (∀ p, Differentiable ℂ (fun z => G z p)) ∧
      (∀ z ∈ tube Ω, ∀ p, G z p = F z p) ∧
      Continuous (Function.uncurry G) ∧
      (∀ K : Set (ι → ℂ), IsCompact K → ∃ C : ℝ, ∀ z ∈ K, ∀ p, ‖G z p‖ ≤ C * h p) := by sorry

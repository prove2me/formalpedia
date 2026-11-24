-- Prove2me | Theorems.Thm_EisTube_psi_bound_all
-- name    : EisTube.psi_bound_all
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:21:21.083296+00:00
-- url     : https://prove2.me/theorems/aec34663-dae6-45a2-bf38-049e82ba9d23
-- title:
--   Eis Tube: psi bound all
-- statement:
--   The Eis Tube construction uses the psi bound all property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/EisensteinSeriesG2/TubeDomainExtension/TubeExtendsFarCone.lean#L198-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/EisensteinSeriesG2/TubeDomainExtension/TubeExtendsFarCone.lean#L198-L231

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

theorem EisTube.psi_bound_all {Ω : Set (ι → ℝ)} (hΩo : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hmid : ∀ x : ι → ℝ, ∃ x₁ ∈ Ω, ∃ x₂ ∈ Ω, x = midpoint ℝ x₁ x₂)
    {h : P → ℝ} (h0 : ∀ p, 0 ≤ h p) {F : (ι → ℂ) → P → ℂ}
    (hhol : ∀ p, DifferentiableOn ℂ (fun z => F z p) (tube Ω))
    (hbd : ∀ K ⊆ Ω, IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ z : ι → ℂ, reV z ∈ K → ∀ p,
      ‖F z p‖ ≤ C * h p * (1 + ‖imV z‖) ^ N)
    {x₀ : ι → ℝ} (h₀ : x₀ ∈ Ω) (v : ι → ℝ) :
    ∃ M : ℝ, ∀ p t, ‖psiAt F x₀ p t‖ ≤ M * h p * Real.exp (-(2 * Real.pi * ∑ i, v i * t i)) := by sorry

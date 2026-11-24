-- Prove2me | Theorems.Thm_EisTube_gf_bound
-- name    : EisTube.gf_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:20:25.808807+00:00
-- url     : https://prove2.me/theorems/8d44fafe-0c58-4cb8-b0fd-a4d7956f93c8
-- title:
--   Eis Tube: gf bound
-- statement:
--   The Eis Tube construction uses the gf bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/EisensteinSeriesG2/TubeDomainExtension/TubeExtendsFarCone.lean#L91-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/EisensteinSeriesG2/TubeDomainExtension/TubeExtendsFarCone.lean#L91-L125

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

theorem EisTube.gf_bound {Ω : Set (ι → ℝ)} {h : P → ℝ} (h0 : ∀ p, 0 ≤ h p) {F : (ι → ℂ) → P → ℂ}
    (hbd : ∀ K ⊆ Ω, IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ z : ι → ℂ, reV z ∈ K → ∀ p,
      ‖F z p‖ ≤ C * h p * (1 + ‖imV z‖) ^ N)
    {K : Set (ι → ℝ)} (hK : K ⊆ Ω) (hKc : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ (y : ι → ℝ) p,
      ‖gf F (cz x y) p‖ ≤ C * h p * Real.exp (-(∑ i, y i ^ 2) / 2) := by sorry

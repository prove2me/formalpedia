-- Prove2me | Theorems.Thm_CompanionTheory_LimBd_URep_exists_to_L2
-- name    : CompanionTheory.LimBd.URep.exists_to_L2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:32:34.399867+00:00
-- url     : https://prove2.me/theorems/1c680770-925c-4eb1-a0d8-2240265b2554
-- title:
--   URep: exists to L2
-- statement:
--   The URep construction uses the exists to L2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/SchurOrthogonality/SchurOrthogonality.lean#L18-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/SchurOrthogonality/SchurOrthogonality.lean#L18-L40

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_URepSchur
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurOrthogonality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
open CompanionTheory CompanionTheory.LimBd CompanionTheory.LimBd.URep
open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem CompanionTheory.LimBd.URep.exists_to_L2 (Φ : X → (H →L[ℂ] ℂ)) (hΦ : ∀ v, MemLp (fun x => Φ x v) 2 μ) :
    ∃ T : H →L[ℂ] Lp ℂ 2 μ, ∀ v, (T v : X → ℂ) =ᵐ[μ] fun x => Φ x v := by sorry

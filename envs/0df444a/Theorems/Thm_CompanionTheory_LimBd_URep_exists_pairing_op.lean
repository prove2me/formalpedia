-- Prove2me | Theorems.Thm_CompanionTheory_LimBd_URep_exists_pairing_op
-- name    : CompanionTheory.LimBd.URep.exists_pairing_op
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:56:50.879011+00:00
-- url     : https://prove2.me/theorems/ffce9a5d-8eae-4a47-b259-070e29637c40
-- title:
--   URep: exists pairing op
-- statement:
--   The URep construction uses the exists pairing op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/SchurOrthogonality/SchurOrthogonality.lean#L42-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/SchurOrthogonality/SchurOrthogonality.lean#L42-L52

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

theorem CompanionTheory.LimBd.URep.exists_pairing_op (Φ : X → (H →L[ℂ] ℂ)) (hΦ : ∀ v, MemLp (fun x => Φ x v) 2 μ)
    (Ψ : X → (K →L[ℂ] ℂ)) (hΨ : ∀ v, MemLp (fun x => Ψ x v) 2 μ) :
    ∃ A : H →L[ℂ] K, ∀ v v', ∫ x, Φ x v * star (Ψ x v') ∂μ = ⟪v', A v⟫_ℂ := by sorry

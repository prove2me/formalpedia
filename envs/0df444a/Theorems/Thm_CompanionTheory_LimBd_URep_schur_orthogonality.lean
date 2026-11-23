-- Prove2me | Theorems.Thm_CompanionTheory_LimBd_URep_schur_orthogonality
-- name    : CompanionTheory.LimBd.URep.schur_orthogonality
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:32:25.537949+00:00
-- url     : https://prove2.me/theorems/2da9a903-a287-4081-97f4-7a15258372f8
-- title:
--   URep: schur orthogonality
-- statement:
--   The URep construction uses the schur orthogonality property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/SchurOrthogonality/SchurOrthogonality.lean#L181-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/SchurOrthogonality/SchurOrthogonality.lean#L181-L211

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
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem CompanionTheory.LimBd.URep.schur_orthogonality {π : UnitaryRep G H} (hirr : π.IsIrreducible) (hπ : SqInt μ π) :
    ∃ d : ℝ, 0 < d ∧ ∀ v w v' w' : H, pairing μ π π v w v' w' = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ) := by sorry

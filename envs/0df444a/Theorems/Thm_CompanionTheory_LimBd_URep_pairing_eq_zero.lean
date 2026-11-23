-- Prove2me | Theorems.Thm_CompanionTheory_LimBd_URep_pairing_eq_zero
-- name    : CompanionTheory.LimBd.URep.pairing_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:31:52.868553+00:00
-- url     : https://prove2.me/theorems/9f4fcc53-f64a-43a4-8fe5-ea29de426679
-- title:
--   URep: pairing eq zero
-- statement:
--   The URep construction uses the pairing eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/SchurOrthogonality/SchurOrthogonality.lean#L213-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/SchurOrthogonality/SchurOrthogonality.lean#L213-L218

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

theorem CompanionTheory.LimBd.URep.pairing_eq_zero {π : UnitaryRep G H} {σ : UnitaryRep G K} (hπi : π.IsIrreducible)
    (hσi : σ.IsIrreducible) (hπ : SqInt μ π) (hσ : SqInt μ σ) (hne : ¬ π.IsEquivalent σ)
    (v w : H) (v' w' : K) : pairing μ π σ v w v' w' = 0 := by sorry

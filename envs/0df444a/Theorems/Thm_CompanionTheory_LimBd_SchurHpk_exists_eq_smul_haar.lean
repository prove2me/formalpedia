-- Prove2me | Theorems.Thm_CompanionTheory_LimBd_SchurHpk_exists_eq_smul_haar
-- name    : CompanionTheory.LimBd.SchurHpk.exists_eq_smul_haar
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T15:57:41.562906+00:00
-- url     : https://prove2.me/theorems/d931de6d-8be6-40b4-b3c8-8c6659b2c51c
-- title:
--   Schur Hpk: exists eq smul haar
-- statement:
--   The Schur Hpk construction uses the exists eq smul haar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/SchurOrthogonality/SchurH.lean#L11-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/SchurOrthogonality/SchurH.lean#L11-L30

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurOrthogonality
import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurH
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.LimBd CompanionTheory.LimBd.SchurHpk
open MeasureTheory Matrix Topology PI.UpqRep CompanionTheory.LimBd.URep
open scoped InnerProductSpace ENNReal

theorem CompanionTheory.LimBd.SchurHpk.exists_eq_smul_haar {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (ν μ : Measure G)
    [SigmaFinite ν] [ν.IsMulLeftInvariant] (hν : ν ≠ 0) [μ.IsHaarMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ ν = c • μ := by sorry

-- Prove2me | Theorems.Thm_Formalism_L2_SG_AvgPf_isFD_of_strict
-- name    : Formalism.L2.SG.AvgPf.isFD_of_strict
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:06.041121+00:00
-- url     : https://prove2.me/theorems/ef7f2043-758b-463c-96b7-dc52e356f5ab
-- title:
--   Avg Pf: is FD of strict
-- statement:
--   The Avg Pf construction uses the is FD of strict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/LieAveraging/LsSetresAvg.lean#L10-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/LieAveraging/LsSetresAvg.lean#L10-L25

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_LieAveraging_LsSetresAvg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Topology Set
open scoped Pointwise ENNReal
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.AvgPf

theorem Formalism.L2.SG.AvgPf.isFD_of_strict {Γ α : Type*} [Group Γ] [MulAction Γ α] [MeasurableSpace α] (μ : Measure α) {S : Set α}
    (hS : MeasurableSet S) (hcov : ∀ᵐ x ∂μ, ∃ g : Γ, g • x ∈ S)
    (huniq : ∀ x ∈ S, ∀ g : Γ, g • x ∈ S → g = 1) : IsFundamentalDomain Γ S μ := by sorry

-- Prove2me | Theorems.Thm_Formalism_L2_SG_AvgPf_exists_fd
-- name    : Formalism.L2.SG.AvgPf.exists_fd
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:06.957838+00:00
-- url     : https://prove2.me/theorems/e0c24ff0-fc4f-4342-b113-d29ffb1a2bff
-- title:
--   Avg Pf: exists fd
-- statement:
--   The Avg Pf construction uses the exists fd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/LieAveraging/LsSetresAvg.lean#L36-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/LieAveraging/LsSetresAvg.lean#L36-L94

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
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem Formalism.L2.SG.AvgPf.exists_fd (R Γ : Subgroup G) (hR : IsClosed (R : Set G)) (hΓR : Γ ≤ R) [DiscreteTopology Γ] [Countable Γ]
    (K : Set G) (hK : IsCompact K) (hKc : ∀ r ∈ R, ∃ s ∈ Γ, s * r ∈ K) :
    ∃ D : Set G, MeasurableSet D ∧ D ⊆ K ∧ D ⊆ (R : Set G) ∧ (∀ r ∈ R, ∃ s ∈ Γ, s * r ∈ D) ∧
      (∀ r ∈ D, ∀ s ∈ Γ, s * r ∈ D → s = 1) := by sorry

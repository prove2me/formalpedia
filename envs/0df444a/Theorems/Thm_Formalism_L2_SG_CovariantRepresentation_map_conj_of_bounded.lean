-- Prove2me | Theorems.Thm_Formalism_L2_SG_CovariantRepresentation_map_conj_of_bounded
-- name    : Formalism.L2.SG.CovariantRepresentation.map_conj_of_bounded
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:15.716647+00:00
-- url     : https://prove2.me/theorems/fd5e70f7-325f-45dc-b8c4-82472d2d725f
-- title:
--   Covariant Representation: map conj of bounded
-- statement:
--   The Covariant Representation construction uses the map conj of bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/MapConjOfBounded.lean#L27-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/MapConjOfBounded.lean#L27-L117

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_IsMulRightInvariantOfLattice
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_MapConjOfBounded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Measure Set Filter Topology
open scoped ENNReal NNReal Pointwise
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.CovariantRepresentation
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem Formalism.L2.SG.CovariantRepresentation.map_conj_of_bounded (R : Subgroup G) (hR : IsClosed (R : Set G)) (ν : Measure G) (h0 : ν ≠ 0)
    (hc : ν (R : Set G)ᶜ = 0) (hK : ∀ K : Set G, IsCompact K → ν K < ⊤)
    (hl : ∀ r ∈ R, ν.map (fun x => r * x) = ν) (k : G) (hk : ∀ r, r ∈ R ↔ k⁻¹ * r * k ∈ R)
    (hC : ∃ C : Set G, IsCompact C ∧ ∀ m : ℤ, k ^ m ∈ C) : ν.map (fun x => k⁻¹ * x * k) = ν := by sorry

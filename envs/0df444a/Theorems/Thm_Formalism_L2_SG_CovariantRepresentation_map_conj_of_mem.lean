-- Prove2me | Theorems.Thm_Formalism_L2_SG_CovariantRepresentation_map_conj_of_mem
-- name    : Formalism.L2.SG.CovariantRepresentation.map_conj_of_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:01.699861+00:00
-- url     : https://prove2.me/theorems/669548f6-2af5-4e01-a4bd-29a644fcd908
-- title:
--   Covariant Representation: map conj of mem
-- statement:
--   The Covariant Representation construction uses the map conj of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/MapConjOfBounded.lean#L16-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/MapConjOfBounded.lean#L16-L25

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

theorem Formalism.L2.SG.CovariantRepresentation.map_conj_of_mem (R : Subgroup G) (ν : Measure G) (hl : ∀ r ∈ R, ν.map (fun x => r * x) = ν)
    (hi : ν.map (fun x => x⁻¹) = ν) {n : G} (hn : n ∈ R) : ν.map (fun x => n⁻¹ * x * n) = ν := by sorry

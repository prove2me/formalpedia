-- Prove2me | Theorems.Thm_Formalism_L2_SG_CovariantRepresentation_haar_map_mul_right_of_lattice
-- name    : Formalism.L2.SG.CovariantRepresentation.haar_map_mul_right_of_lattice
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:31:21.186958+00:00
-- url     : https://prove2.me/theorems/7fbab33c-ce05-4f2d-b88c-dc8a3c9bdd21
-- title:
--   Covariant Representation: haar map mul right of lattice
-- statement:
--   The Covariant Representation construction uses the haar map mul right of lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/IsMulRightInvariantOfLattice.lean#L128-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/IsMulRightInvariantOfLattice.lean#L128-L173

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_IsMulRightInvariantOfLattice
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
variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
  [LocallyCompactSpace H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

theorem Formalism.L2.SG.CovariantRepresentation.haar_map_mul_right_of_lattice (μ : Measure H) [IsHaarMeasure μ] (Γ : Subgroup H) [Countable Γ]
    [DiscreteTopology Γ] {K : Set H} (hK : IsCompact K) (hcov : ∀ x : H, ∃ s ∈ Γ, s * x ∈ K) (g : H) :
    μ.map (· * g) = μ := by sorry

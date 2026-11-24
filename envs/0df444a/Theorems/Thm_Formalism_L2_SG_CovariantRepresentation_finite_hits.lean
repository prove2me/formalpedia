-- Prove2me | Theorems.Thm_Formalism_L2_SG_CovariantRepresentation_finite_hits
-- name    : Formalism.L2.SG.CovariantRepresentation.finite_hits
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:42.746927+00:00
-- url     : https://prove2.me/theorems/639f50c1-8971-4cfd-8429-6484423241fb
-- title:
--   Covariant Representation: finite hits
-- statement:
--   The Covariant Representation construction uses the finite hits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/IsMulRightInvariantOfLattice.lean#L19-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/IsMulRightInvariantOfLattice.lean#L19-L27

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

theorem Formalism.L2.SG.CovariantRepresentation.finite_hits (Γ : Subgroup H) [DiscreteTopology Γ] {K : Set H} (hK : IsCompact K) (x : H) :
    {γ : Γ | (γ : H) * x ∈ K}.Finite := by sorry

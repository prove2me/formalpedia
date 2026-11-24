-- Prove2me | Theorems.Thm_Formalism_L2_SG_CovariantRepresentation_lcount_ne_top
-- name    : Formalism.L2.SG.CovariantRepresentation.lcount_ne_top
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:27.299539+00:00
-- url     : https://prove2.me/theorems/2ee9746e-baf7-408e-83f6-159cb4271c72
-- title:
--   Covariant Representation: lcount ne top
-- statement:
--   The Covariant Representation construction uses the lcount ne top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/IsMulRightInvariantOfLattice.lean#L29-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/IsMulRightInvariantOfLattice.lean#L29-L38

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

theorem Formalism.L2.SG.CovariantRepresentation.lcount_ne_top (Γ : Subgroup H) [DiscreteTopology Γ] {K : Set H} (hK : IsCompact K) (x : H) :
    lcount Γ K x ≠ ∞ := by sorry

-- Prove2me | Theorems.Thm_Formalism_L2_SG_CovariantRepresentation_measurable_lcount
-- name    : Formalism.L2.SG.CovariantRepresentation.measurable_lcount
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:02.698402+00:00
-- url     : https://prove2.me/theorems/dc293e9c-3f93-4152-a94e-9b765e029a38
-- title:
--   Covariant Representation: measurable lcount
-- statement:
--   The Covariant Representation construction uses the measurable lcount property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/IsMulRightInvariantOfLattice.lean#L52-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/IsMulRightInvariantOfLattice.lean#L52-L55

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

theorem Formalism.L2.SG.CovariantRepresentation.measurable_lcount (Γ : Subgroup H) [Countable Γ] {K : Set H} (hK : IsCompact K) :
    Measurable (lcount Γ K) := by sorry

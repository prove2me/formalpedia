-- Prove2me | Theorems.Thm_Formalism_L2_SG_CovariantRepresentation_tsum_lwt
-- name    : Formalism.L2.SG.CovariantRepresentation.tsum_lwt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:27.65586+00:00
-- url     : https://prove2.me/theorems/f065d2cb-bf70-4177-a1de-e865adc0b95c
-- title:
--   Covariant Representation: tsum lwt
-- statement:
--   The Covariant Representation construction uses the tsum lwt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/IsMulRightInvariantOfLattice.lean#L61-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/IsMulRightInvariantOfLattice.lean#L61-L66

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

theorem Formalism.L2.SG.CovariantRepresentation.tsum_lwt (Γ : Subgroup H) [DiscreteTopology Γ] {K : Set H} (hK : IsCompact K)
    (hcov : ∀ x : H, ∃ s ∈ Γ, s * x ∈ K) (x : H) : ∑' γ : Γ, lwt Γ K ((γ : H) * x) = 1 := by sorry

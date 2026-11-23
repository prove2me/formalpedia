-- Prove2me | Theorems.Thm_Formalism_L2_G_Pend_norm_wToC_le
-- name    : Formalism.L2.G.Pend.norm_wToC_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:28:42.829306+00:00
-- url     : https://prove2.me/theorems/d406fac6-0f1b-44b3-a551-09863e4cac0f
-- title:
--   Pend: norm w To C le
-- statement:
--   The Pend construction uses the norm w To C le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/PendingLemmas/WittFractionToCpAlgebraMap.lean#L326-L326
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/PendingLemmas/WittFractionToCpAlgebraMap.lean#L326-L326

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PerfectRings_IsLocalRingOfComplete
import Definitions.Def_Lemmata_FirstBlockLemmaF_Imports
import Definitions.Def_Lemmata_GeneralBFactThird_Imports
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PendingLemmas_WittFractionToCpAlgebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial IsLocalRing Filter Topology
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Pend
variable (p : ℕ) [hp : Fact p.Prime]
attribute [local instance] algZW algQK
attribute [local instance] Formalism.L2.G.Pend.towerZQK

theorem Formalism.L2.G.Pend.norm_wToC_le (x : WW p) : ‖wToC p x‖ ≤ 1 := by sorry

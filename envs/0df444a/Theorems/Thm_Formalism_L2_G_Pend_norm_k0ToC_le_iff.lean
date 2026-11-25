-- Prove2me | Theorems.Thm_Formalism_L2_G_Pend_norm_k0ToC_le_iff
-- name    : Formalism.L2.G.Pend.norm_k0ToC_le_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:45:40.790881+00:00
-- url     : https://prove2.me/theorems/f84810be-0e94-411d-b763-bd01d53f5285
-- title:
--   Pend: norm k0 To C le iff
-- statement:
--   The Pend construction uses the norm k0 To C le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/PendingLemmas/WittFractionToCpAlgebraMap.lean#L343-L366
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/PendingLemmas/WittFractionToCpAlgebraMap.lean#L343-L366

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

theorem Formalism.L2.G.Pend.norm_k0ToC_le_iff (x : K0 p) : ‖k0ToC p x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap (WW p) (K0 p)) := by sorry

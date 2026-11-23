-- Prove2me | Theorems.Thm_Formalism_L2_G_Pend_witt_fraction_to_Cp_algebraMap
-- name    : Formalism.L2.G.Pend.witt_fraction_to_Cp_algebraMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:28:18.269803+00:00
-- url     : https://prove2.me/theorems/75e6a26d-5b4e-4eb3-a644-dd04bc88ec15
-- title:
--   Pend: witt fraction to Cp algebra Map
-- statement:
--   The Pend construction uses the witt fraction to Cp algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/PendingLemmas/WittFractionToCpAlgebraMap.lean#L340-L341
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/PendingLemmas/WittFractionToCpAlgebraMap.lean#L340-L341

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

theorem Formalism.L2.G.Pend.witt_fraction_to_Cp_algebraMap (x : WW p) : k0ToC p (algebraMap (WW p) (K0 p) x) = wToC p x := by sorry

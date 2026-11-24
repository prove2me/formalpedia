-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Stab_exists_open_normal_orderOf
-- name    : Formalism.FrobeniusOrbits.Stab.exists_open_normal_orderOf
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T14:31:41.562446+00:00
-- url     : https://prove2.me/theorems/1b4ae765-3109-4f42-b863-5df1fec70088
-- title:
--   Stab: exists open normal order Of
-- statement:
--   The Stab construction uses the exists open normal order Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ExistsOpenNormalOrderOf.lean#L13-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ExistsOpenNormalOrderOf.lean#L13-L36

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ExistsOpenNormalOrderOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Stab

theorem Formalism.FrobeniusOrbits.Stab.exists_open_normal_orderOf {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    (x : G) (hx : IsOfFinOrder x) :
    ∃ N : OpenNormalSubgroup G,
      orderOf (QuotientGroup.mk x : G ⧸ (N.toSubgroup)) = orderOf x := by sorry

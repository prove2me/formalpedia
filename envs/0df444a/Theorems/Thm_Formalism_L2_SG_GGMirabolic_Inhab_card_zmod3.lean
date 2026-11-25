-- Prove2me | Theorems.Thm_Formalism_L2_SG_GGMirabolic_Inhab_card_zmod3
-- name    : Formalism.L2.SG.GGMirabolic.Inhab.card_zmod3
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:47:25.549867+00:00
-- url     : https://prove2.me/theorems/576a89b1-74b8-593a-aa36-2924530b6e4a
-- title:
--   Inhab: card zmod3
-- statement:
--   The Inhab construction uses the card zmod3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GGMirabolicInhab.lean#L33-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GGMirabolicInhab.lean#L33-L33

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolicInhab
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.GGMirabolic Formalism.L2.SG.GGMirabolic.Inhab
open Formalism.L2.SG.GGMirabolic
noncomputable section
open Classical

theorem Formalism.L2.SG.GGMirabolic.Inhab.card_zmod3 : 3 ≤ Fintype.card (ZMod 3) := by sorry

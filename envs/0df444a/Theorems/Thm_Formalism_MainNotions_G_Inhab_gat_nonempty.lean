-- Prove2me | Theorems.Thm_Formalism_MainNotions_G_Inhab_gat_nonempty
-- name    : Formalism.MainNotions.G.Inhab.gat_nonempty
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:57:53.082881+00:00
-- url     : https://prove2.me/theorems/f041268c-240c-5277-9301-dbe1db40fa7c
-- title:
--   Inhab: gat nonempty
-- statement:
--   The Inhab construction uses the gat nonempty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TensorLatticeBounds/DataLoc.lean#L224-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TensorLatticeBounds/DataLoc.lean#L224-L227

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataGChain
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_GatSetting
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.Inhab
open Formalism.MainNotions.G

theorem Formalism.MainNotions.G.Inhab.gat_nonempty (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
    ∃ G : GAtP p, 1 ≤ G.P.nV ∧ Nonempty G.comp ∧ G.TrivStab ∧ G.FinClasses := by sorry

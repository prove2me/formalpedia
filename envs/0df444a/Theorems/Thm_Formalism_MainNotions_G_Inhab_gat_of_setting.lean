-- Prove2me | Theorems.Thm_Formalism_MainNotions_G_Inhab_gat_of_setting
-- name    : Formalism.MainNotions.G.Inhab.gat_of_setting
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T09:56:29.775134+00:00
-- url     : https://prove2.me/theorems/8f61386c-4046-4fec-b826-c311f38c453a
-- title:
--   Inhab: gat of setting
-- statement:
--   The Inhab construction uses the gat of setting property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TensorLatticeBounds/DataLoc.lean#L199-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TensorLatticeBounds/DataLoc.lean#L199-L201

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
variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

theorem Formalism.MainNotions.G.Inhab.gat_of_setting (h : HidaSetting p n' W Qq O Kf ι σ j w) :
    ∃ G : GAtP p, 1 ≤ G.P.nV ∧ Nonempty G.comp ∧ G.TrivStab ∧ G.FinClasses := by sorry

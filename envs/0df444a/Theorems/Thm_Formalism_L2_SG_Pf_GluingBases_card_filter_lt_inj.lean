-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_GluingBases_card_filter_lt_inj
-- name    : Formalism.L2.SG.Pf.GluingBases.card_filter_lt_inj
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:08:52.664579+00:00
-- url     : https://prove2.me/theorems/b73dcd47-1414-57c0-a73b-a0bf4f65030a
-- title:
--   Gluing Bases: card filter lt inj
-- statement:
--   The Gluing Bases construction uses the card filter lt inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/CardFilterLtInj.lean#L14-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/CardFilterLtInj.lean#L14-L31

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_IsGlueDataPre
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsTotPosCongr
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsPrescFamily
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_CardFilterLtInj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.GluingBases
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU

theorem Formalism.L2.SG.Pf.GluingBases.card_filter_lt_inj {n : ℕ} (P : Finset (Fin n)) {i k : Fin n} (hi : i ∈ P) (hk : k ∈ P)
    (e : (P.filter (· < i)).card = (P.filter (· < k)).card) : i = k := by sorry

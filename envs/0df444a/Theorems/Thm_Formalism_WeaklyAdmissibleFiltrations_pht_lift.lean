-- Prove2me | Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_pht_lift
-- name    : Formalism.WeaklyAdmissibleFiltrations.pht_lift
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:55:03.343857+00:00
-- url     : https://prove2.me/theorems/739ddd56-de4d-4f3a-8117-ecad6990d57b
-- title:
--   Weakly Admissible Filtrations: pht lift
-- statement:
--   The Weakly Admissible Filtrations construction uses the pht lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/PhtGalois.lean#L25-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/PhtGalois.lean#L25-L26

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_Window
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_JumpsPFilAntitoneOfLe
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_RankOne
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_ExwaFiltrationNegOneEqSpanSingle
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_Galois
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_TrivCrys
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_ExLattice
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_ExistsPeriodRingDataHolds
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_WachCol
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_LiftGal
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_NegJumps
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_DPotCrisStableAndExistsPotentiallyCrystallineDat
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_WindowCountIcoTelescope
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_PhtGalois
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.WeaklyAdmissibleFiltrations

theorem Formalism.WeaklyAdmissibleFiltrations.pht_lift : LiftGal ∧ NegJumps ∧ WindowCount := by sorry

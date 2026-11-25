-- Prove2me | Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_pht_pc
-- name    : Formalism.WeaklyAdmissibleFiltrations.pht_pc
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:57:27.908927+00:00
-- url     : https://prove2.me/theorems/969a8fe2-2ca3-40f2-b950-02743974d3e7
-- title:
--   Weakly Admissible Filtrations: pht pc
-- statement:
--   The Weakly Admissible Filtrations construction uses the pht pc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/PhtGalois.lean#L28-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/PhtGalois.lean#L28-L28

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

theorem Formalism.WeaklyAdmissibleFiltrations.pht_pc : DpcrisStable ∧ ExPC := by sorry

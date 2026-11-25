-- Prove2me | Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_pht_filphi
-- name    : Formalism.WeaklyAdmissibleFiltrations.pht_filphi
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:53:28.454521+00:00
-- url     : https://prove2.me/theorems/5b8f8caf-f30a-456f-80f2-9189f38ab663
-- title:
--   Weakly Admissible Filtrations: pht filphi
-- statement:
--   The Weakly Admissible Filtrations construction uses the pht filphi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/PhtGalois.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/PhtGalois.lean#L17-L19

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

theorem Formalism.WeaklyAdmissibleFiltrations.pht_filphi : THWindow ∧ DimSum ∧ JumpsIcc ∧ SubTopBot ∧ RankOneWA ∧ ExWA := by sorry

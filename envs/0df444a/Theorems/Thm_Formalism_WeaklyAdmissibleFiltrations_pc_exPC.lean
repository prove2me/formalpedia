-- Prove2me | Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_pc_exPC
-- name    : Formalism.WeaklyAdmissibleFiltrations.pc_exPC
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:39:46.446797+00:00
-- url     : https://prove2.me/theorems/757133b1-bafd-4b06-baf3-6435452d2ab7
-- title:
--   Weakly Admissible Filtrations: pc ex PC
-- statement:
--   The Weakly Admissible Filtrations construction uses the pc ex PC property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/DPotCrisStableAndExistsPotentiallyCrystallineDat.lean#L121-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/DPotCrisStableAndExistsPotentiallyCrystallineDat.lean#L121-L124

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_DpcrisStable
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_DPotCrisStableAndExistsPotentiallyCrystallineDat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.WeaklyAdmissibleFiltrations
open Module TensorProduct

theorem Formalism.WeaklyAdmissibleFiltrations.pc_exPC : ExPC := by sorry

-- Prove2me | Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_dPotCrisStable_and_existsPotentiallyCrystallineData
-- name    : Formalism.WeaklyAdmissibleFiltrations.dPotCrisStable_and_existsPotentiallyCrystallineData
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:39:25.518307+00:00
-- url     : https://prove2.me/theorems/8a5344b5-751d-42c5-ad67-ebf5439fea5b
-- title:
--   Weakly Admissible Filtrations: d Pot Cris Stable and exists Potentially Crystalline Data
-- statement:
--   The Weakly Admissible Filtrations construction uses the d Pot Cris Stable and exists Potentially Crystalline Data property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/DPotCrisStableAndExistsPotentiallyCrystallineDat.lean#L126-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/DPotCrisStableAndExistsPotentiallyCrystallineDat.lean#L126-L126

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

theorem Formalism.WeaklyAdmissibleFiltrations.dPotCrisStable_and_existsPotentiallyCrystallineData : DpcrisStable ∧ ExPC := by sorry

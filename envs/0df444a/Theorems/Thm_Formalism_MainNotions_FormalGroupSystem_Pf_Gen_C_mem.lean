-- Prove2me | Theorems.Thm_Formalism_MainNotions_FormalGroupSystem_Pf_Gen_C_mem
-- name    : Formalism.MainNotions.FormalGroupSystem.Pf.Gen.C_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T09:54:34.791995+00:00
-- url     : https://prove2.me/theorems/e11aa9c2-82b0-4b55-8a19-a170807b0646
-- title:
--   Gen: C mem
-- statement:
--   The Gen construction uses the C mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/JpSubstExpand.lean#L60-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/JpSubstExpand.lean#L60-L67

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MultisetValuation_CoeffProdRename
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MultisetValuation_JpSubstExpand
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.FormalGroupSystem.Pf Formalism.MainNotions.FormalGroupSystem.Pf.Gen
open Finset
variable {R σ Pl : Type} [CommRing R]

theorem Formalism.MainNotions.FormalGroupSystem.Pf.Gen.C_mem {π : σ → Pl} {v : Pl} (c : R) : (MvPowerSeries.C c : MvPowerSeries σ R) ∈ SuppOn π v := by sorry

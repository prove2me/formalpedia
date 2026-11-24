-- Prove2me | Theorems.Thm_Formalism_MainNotions_BridgeLevelGen_finrank_E
-- name    : Formalism.MainNotions.BridgeLevelGen.finrank_E
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T14:59:09.699208+00:00
-- url     : https://prove2.me/theorems/ea8b3f00-3128-47bb-97b6-9da0a9bcf445
-- title:
--   Bridge Level Gen: finrank E
-- statement:
--   The Bridge Level Gen construction uses the finrank E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLevelGen.lean#L13-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLevelGen.lean#L13-L16

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLevelIdx
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLevelGenA
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLevelGenB
import Definitions.Def_Formalism_FlagUnipotentLattices_FlagUnipotentLatticeOfRel
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLevelGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLevelGen
open MeasureTheory NumberField Formalism.MainNotions.S Formalism.MainNotions.BridgeLevelIdx
open scoped ENNReal TensorProduct

theorem Formalism.MainNotions.BridgeLevelGen.finrank_E (I : AutInst) : Module.finrank ℚ I.E = 2 * I.f := by sorry

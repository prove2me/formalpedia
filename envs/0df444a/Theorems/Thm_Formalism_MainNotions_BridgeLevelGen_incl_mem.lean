-- Prove2me | Theorems.Thm_Formalism_MainNotions_BridgeLevelGen_incl_mem
-- name    : Formalism.MainNotions.BridgeLevelGen.incl_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:00:01.274107+00:00
-- url     : https://prove2.me/theorems/e6a4dc1b-1a8c-4f5d-b0bb-c4b227136c63
-- title:
--   Bridge Level Gen: incl mem
-- statement:
--   The Bridge Level Gen construction uses the incl mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLevelGen.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLevelGen.lean#L18-L20

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

theorem Formalism.MainNotions.BridgeLevelGen.incl_mem (I : AutInst) (b : 𝓞 I.E) :
    Formalism.UG.inclE (F := I.F) (Af I.F) (algebraMap (𝓞 I.E) I.E b) ∈ IntAf I.F I.E := by sorry

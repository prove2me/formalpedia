-- Prove2me | Theorems.Thm_Formalism_IndefR_LocBrg_mem_intL
-- name    : Formalism.IndefR.LocBrg.mem_intL
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:15.159235+00:00
-- url     : https://prove2.me/theorems/ac0ce27b-ac84-4ebc-856e-ece5119e2ca2
-- title:
--   Loc Brg: mem int L
-- statement:
--   The Loc Brg construction uses the mem int L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LocalNormSurjectivity/MemMaxVAIff.lean#L28-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LocalNormSurjectivity/MemMaxVAIff.lean#L28-L28

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LocalNormSurjectivity_WittDiag
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LocalNormSurjectivity_FinNormSurj
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LocalNormSurjectivity_MemMaxVAIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.IndefR Formalism.IndefR.LocBrg
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem Formalism.IndefR.LocBrg.mem_intL {x : L} : x ∈ Formalism.UG.intL L ↔ Valued.v x ≤ 1 := by sorry

-- Prove2me | Theorems.Thm_Formalism_IndefR_LocBrg_mem_max_VA_iff
-- name    : Formalism.IndefR.LocBrg.mem_max_VA_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:53:31.482841+00:00
-- url     : https://prove2.me/theorems/4e0f5d87-f80a-4bfe-94de-474cc7e036b4
-- title:
--   Loc Brg: mem max VA iff
-- statement:
--   The Loc Brg construction uses the mem max VA iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LocalNormSurjectivity/MemMaxVAIff.lean#L54-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LocalNormSurjectivity/MemMaxVAIff.lean#L54-L56

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

theorem Formalism.IndefR.LocBrg.mem_max_VA_iff (a : VA L) : a ∈ IsLocalRing.maximalIdeal (VA L) ↔ Valued.v (a : L) < 1 := by sorry

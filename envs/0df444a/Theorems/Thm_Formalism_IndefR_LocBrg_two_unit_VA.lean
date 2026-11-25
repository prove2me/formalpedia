-- Prove2me | Theorems.Thm_Formalism_IndefR_LocBrg_two_unit_VA
-- name    : Formalism.IndefR.LocBrg.two_unit_VA
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:42:04.964132+00:00
-- url     : https://prove2.me/theorems/3e279207-e5be-44dc-8385-3addc089e9fb
-- title:
--   Loc Brg: two unit VA
-- statement:
--   The Loc Brg construction uses the two unit VA property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LocalNormSurjectivity/MemMaxVAIff.lean#L122-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LocalNormSurjectivity/MemMaxVAIff.lean#L122-L127

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

theorem Formalism.IndefR.LocBrg.two_unit_VA {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : Formalism.UG.IsUnramInv ϖ σ q) (hq : Odd q) :
    IsUnit (2 : VA L) := by sorry

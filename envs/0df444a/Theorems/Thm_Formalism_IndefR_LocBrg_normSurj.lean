-- Prove2me | Theorems.Thm_Formalism_IndefR_LocBrg_normSurj
-- name    : Formalism.IndefR.LocBrg.normSurj
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:41:54.097936+00:00
-- url     : https://prove2.me/theorems/11856897-70d9-4a6c-b249-e8008121c5a8
-- title:
--   Loc Brg: norm Surj
-- statement:
--   The Loc Brg construction uses the norm Surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LocalNormSurjectivity/MemMaxVAIff.lean#L133-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LocalNormSurjectivity/MemMaxVAIff.lean#L133-L222

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

theorem Formalism.IndefR.LocBrg.normSurj [CompleteSpace L] (hF : FinNormSurj) (hS : HenselSqrt) {ϖ : L} {σ : L →+* L} {q : ℕ}
    (hU : Formalism.UG.IsUnramInv ϖ σ q) (hq : Odd q) (c : VA L) (hcσ : sigA σ hU.2.1 c = c) (hc : IsUnit c) :
    ∃ t : VA L, sigA σ hU.2.1 t * t = c := by sorry

-- Prove2me | Theorems.Thm_Formalism_IndefR_LocBrg_two_val
-- name    : Formalism.IndefR.LocBrg.two_val
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:12:33.435856+00:00
-- url     : https://prove2.me/theorems/5d002022-11dd-494b-96b4-f18997e62943
-- title:
--   Loc Brg: two val
-- statement:
--   The Loc Brg construction uses the two val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LocalNormSurjectivity/MemMaxVAIff.lean#L129-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LocalNormSurjectivity/MemMaxVAIff.lean#L129-L131

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

theorem Formalism.IndefR.LocBrg.two_val {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : Formalism.UG.IsUnramInv ϖ σ q) (hq : Odd q) :
    Valued.v (2 : L) = 1 := by sorry

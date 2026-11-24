-- Prove2me | Theorems.Thm_Formalism_IndefR_LocBrg_sigA_inv
-- name    : Formalism.IndefR.LocBrg.sigA_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:26.143656+00:00
-- url     : https://prove2.me/theorems/53515da3-550c-421f-bcb5-a85fbe6ecc1d
-- title:
--   Loc Brg: sig A inv
-- statement:
--   The Loc Brg construction uses the sig A inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LocalNormSurjectivity/MemMaxVAIff.lean#L67-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LocalNormSurjectivity/MemMaxVAIff.lean#L67-L69

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
variable (σ : L →+* L) (hv : ∀ x, Valued.v (σ x) = Valued.v x)

theorem Formalism.IndefR.LocBrg.sigA_inv (hσ : ∀ x, σ (σ x) = x) (x : VA L) : sigA σ hv (sigA σ hv x) = x := by sorry

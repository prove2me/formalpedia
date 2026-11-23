-- Prove2me | Theorems.Thm_Formalism_FG_InvIntVAux_Low_mul
-- name    : Formalism.FG.InvIntVAux.Low.mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:42.501494+00:00
-- url     : https://prove2.me/theorems/b26eda4d-4777-4010-80e5-6ce422b7a84a
-- title:
--   Low: mul
-- statement:
--   The Low construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/InvIntV.lean#L25-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/InvIntV.lean#L25-L44

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_InvIntV
import Theorems.Thm_Formalism_G_LogCR_Agree_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
open Formalism Formalism.FG Formalism.FG.InvIntVAux
open Formalism.G Formalism.G.LogCR
variable {K : Type u} [NormedField K]
variable {σ : Type*}

theorem Formalism.FG.InvIntVAux.Low.mul {m k : ℕ} {x y : MvPowerSeries σ K} (hx : Low m x) (hy : Low k y) :
    Low (m + k) (x * y) := by sorry

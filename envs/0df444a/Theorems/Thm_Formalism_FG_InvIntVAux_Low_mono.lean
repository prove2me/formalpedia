-- Prove2me | Theorems.Thm_Formalism_FG_InvIntVAux_Low_mono
-- name    : Formalism.FG.InvIntVAux.Low.mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:15:19.707311+00:00
-- url     : https://prove2.me/theorems/a00c9af0-719a-4dfd-9751-c5b73a02405a
-- title:
--   Low: mono
-- statement:
--   The Low construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/InvIntV.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/InvIntV.lean#L21-L23

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_InvIntV
import Theorems.Thm_Formalism_G_LogCR_Agree_mono

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

theorem Formalism.FG.InvIntVAux.Low.mono {m k : ℕ} {x : MvPowerSeries σ K} (h : Low m x) (hk : k ≤ m) : Low k x := by sorry

-- Prove2me | Theorems.Thm_Formalism_FG_InvIntVAux_low_of_agree
-- name    : Formalism.FG.InvIntVAux.low_of_agree
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:40:08.521224+00:00
-- url     : https://prove2.me/theorems/72a50afd-a428-4a0a-9e49-4b64c043f358
-- title:
--   Inv Int VAux: low of agree
-- statement:
--   The Inv Int VAux construction uses the low of agree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/InvIntV.lean#L69-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/InvIntV.lean#L69-L71

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_InvIntV
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

theorem Formalism.FG.InvIntVAux.low_of_agree {N : ℕ} {a b : MvPowerSeries σ K} (hab : Agree N a b) : Low N (a - b) := by sorry

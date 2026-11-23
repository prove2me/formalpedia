-- Prove2me | Theorems.Thm_Formalism_FG_InvIntVAux_low_one
-- name    : Formalism.FG.InvIntVAux.low_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:22:24.06637+00:00
-- url     : https://prove2.me/theorems/b5540838-4734-4c41-9869-e0bde5f62170
-- title:
--   Inv Int VAux: low one
-- statement:
--   The Inv Int VAux construction uses the low one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/InvIntV.lean#L57-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/InvIntV.lean#L57-L67

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

theorem Formalism.FG.InvIntVAux.low_one {x : MvPowerSeries σ K} (hx : MvPowerSeries.constantCoeff x = 0) : Low 1 x := by sorry

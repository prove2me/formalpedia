-- Prove2me | Theorems.Thm_Formalism_FG_InvIntVAux_tail_low
-- name    : Formalism.FG.InvIntVAux.tail_low
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:40:11.098812+00:00
-- url     : https://prove2.me/theorems/a2275526-4a86-467b-af08-913e3db06329
-- title:
--   Inv Int VAux: tail low
-- statement:
--   The Inv Int VAux construction uses the tail low property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/InvIntV.lean#L291-L305
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/InvIntV.lean#L291-L305

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

theorem Formalism.FG.InvIntVAux.tail_low {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → MvPowerSeries ι K)
    (hf : IsIdMod2 f) (j : ι) : Low 2 (f j - MvPowerSeries.X j) := by sorry

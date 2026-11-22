-- Prove2me | Theorems.Thm_Formalism_FG_InvIntVAux_Low_add
-- name    : Formalism.FG.InvIntVAux.Low.add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:16:05.205556+00:00
-- url     : https://prove2.me/theorems/e618ea3f-f83e-40fd-a819-ae9909a9e04d
-- title:
--   Low: add
-- statement:
--   The Low construction uses the add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/InvIntV.lean#L46-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/InvIntV.lean#L46-L49

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

theorem Formalism.FG.InvIntVAux.Low.add {m : ℕ} {x y : MvPowerSeries σ K} (hx : Low m x) (hy : Low m y) :
    Low m (x + y) := by sorry

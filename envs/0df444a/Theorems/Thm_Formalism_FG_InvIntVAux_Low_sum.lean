-- Prove2me | Theorems.Thm_Formalism_FG_InvIntVAux_Low_sum
-- name    : Formalism.FG.InvIntVAux.Low.sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:58:50.081902+00:00
-- url     : https://prove2.me/theorems/3608762a-bb3f-4776-88af-a9598da723ed
-- title:
--   Low: sum
-- statement:
--   The Low construction uses the sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/InvIntV.lean#L51-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/InvIntV.lean#L51-L55

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

theorem Formalism.FG.InvIntVAux.Low.sum {α : Type*} {m : ℕ} (s : Finset α) (x : α → MvPowerSeries σ K)
    (h : ∀ a ∈ s, Low m (x a)) : Low m (∑ a ∈ s, x a) := by sorry

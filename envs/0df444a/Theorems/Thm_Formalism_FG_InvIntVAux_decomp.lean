-- Prove2me | Theorems.Thm_Formalism_FG_InvIntVAux_decomp
-- name    : Formalism.FG.InvIntVAux.decomp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:40:09.549283+00:00
-- url     : https://prove2.me/theorems/c644322d-04ed-40df-b504-20054123339c
-- title:
--   Inv Int VAux: decomp
-- statement:
--   The Inv Int VAux construction uses the decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/InvIntV.lean#L110-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/InvIntV.lean#L110-L169

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

theorem Formalism.FG.InvIntVAux.decomp {σ : Type*} [Fintype σ] [LinearOrder σ] (m : ℕ) (x : MvPowerSeries σ K)
    (hx : Low (m + 1) x) :
    ∃ y : σ → MvPowerSeries σ K, (∀ i, Low m (y i)) ∧ x = ∑ i, MvPowerSeries.X i * y i := by sorry

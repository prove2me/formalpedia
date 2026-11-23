-- Prove2me | Theorems.Thm_Formalism_FG_InvIntVAux_low_subst_diff
-- name    : Formalism.FG.InvIntVAux.low_subst_diff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:40:15.96227+00:00
-- url     : https://prove2.me/theorems/399ce675-2ff7-4dfd-82c8-f5bd809f4d98
-- title:
--   Inv Int VAux: low subst diff
-- statement:
--   The Inv Int VAux construction uses the low subst diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/InvIntV.lean#L254-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/InvIntV.lean#L254-L289

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

theorem Formalism.FG.InvIntVAux.low_subst_diff {σ τ : Type*} [Fintype σ] [Finite τ] (g : MvPowerSeries σ K)
    (hg : Low 2 g) {N : ℕ} {a b : σ → MvPowerSeries τ K}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) (hab : ∀ i, Agree N (a i) (b i)) :
    Low (N + 1) (MvPowerSeries.subst a g - MvPowerSeries.subst b g) := by sorry

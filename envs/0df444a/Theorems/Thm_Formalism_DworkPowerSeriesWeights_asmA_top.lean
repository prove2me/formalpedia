-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmA_top
-- name    : Formalism.DworkPowerSeriesWeights.asmA_top
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:59:07.386145+00:00
-- url     : https://prove2.me/theorems/6e0d51b6-6716-4ed7-8013-0dd256b009b7
-- title:
--   Dwork Power Series Weights: asm A top
-- statement:
--   The Dwork Power Series Weights construction uses the asm A top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/CapacityLeReachCapacity.lean#L208-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/CapacityLeReachCapacity.lean#L208-L217

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementA
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_PadicValFactorialRatioProd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_CapacityLeReachCapacity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds

theorem Formalism.DworkPowerSeriesWeights.asmA_top (l d : ℕ) [NeZero d] (hl : 2 ≤ l) (TT : Finset (ZMod d))
    (nu1 nu2 : ZMod d → ℕ) (s : ZMod d) (R : Finset ℕ) (hR : ∀ j ∈ R, Odd j) :
    ∃ ε : ℝ, 0 ≤ ε ∧ (∀ e : ℕ, dTop d TT s = e → ((l : ℝ) ^ e)⁻¹ ≤ ε) ∧
      topTerm l d TT nu1 nu2 s + ((nu1 s : ℝ) * ε +
        ∑ j ∈ R, (capL d TT nu1 nu2 (s + (j : ZMod d)) : ℝ) * max (1 - (l : ℝ) ^ j * ε) 0) ≤
        (nu1 s : ℝ) * gam l := by sorry

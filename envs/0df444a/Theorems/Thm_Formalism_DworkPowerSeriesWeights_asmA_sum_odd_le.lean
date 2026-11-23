-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmA_sum_odd_le
-- name    : Formalism.DworkPowerSeriesWeights.asmA_sum_odd_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:59:17.309896+00:00
-- url     : https://prove2.me/theorems/f671dc71-8e59-4fae-bd38-2b27081f4837
-- title:
--   Dwork Power Series Weights: asm A sum odd le
-- statement:
--   The Dwork Power Series Weights construction uses the asm A sum odd le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/CapacityLeReachCapacity.lean#L38-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/CapacityLeReachCapacity.lean#L38-L43

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

theorem Formalism.DworkPowerSeriesWeights.asmA_sum_odd_le (l : ℕ) (hl : 2 ≤ l) (N : Finset ℕ) (hN : ∀ n ∈ N, Odd n) :
    ∑ n ∈ N, ((l : ℝ) ^ n)⁻¹ ≤ gam l := by sorry

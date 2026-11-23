-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmA_cost_nonneg
-- name    : Formalism.DworkPowerSeriesWeights.asmA_cost_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:56:38.072801+00:00
-- url     : https://prove2.me/theorems/0f3a73d1-e377-486b-aa6b-ae4e65718a97
-- title:
--   Dwork Power Series Weights: asm A cost nonneg
-- statement:
--   The Dwork Power Series Weights construction uses the asm A cost nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/CapacityLeReachCapacity.lean#L246-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/CapacityLeReachCapacity.lean#L246-L253

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

theorem Formalism.DworkPowerSeriesWeights.asmA_cost_nonneg (l : ℕ) {d : ℕ} (eps : ZMod d → ℝ) (p : Option (ZMod d × ℤ)) :
    0 ≤ asmA_cost l eps p := by sorry

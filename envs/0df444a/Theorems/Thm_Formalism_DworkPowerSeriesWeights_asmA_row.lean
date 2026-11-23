-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmA_row
-- name    : Formalism.DworkPowerSeriesWeights.asmA_row
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:59:04.757053+00:00
-- url     : https://prove2.me/theorems/0902f113-c7cf-4e67-81c8-c9c93a67843b
-- title:
--   Dwork Power Series Weights: asm A row
-- statement:
--   The Dwork Power Series Weights construction uses the asm A row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/CapacityLeReachCapacity.lean#L255-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/CapacityLeReachCapacity.lean#L255-L276

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

theorem Formalism.DworkPowerSeriesWeights.asmA_row {d : ℕ} {ι : Type} (l : ℕ) (sig eps : ZMod d → ℝ) (hsig : ∀ s, 0 ≤ sig s)
    (lt : ι → ZMod d) (isTop : ι → Bool) (spec : ι → Option (ZMod d × ℤ)) (κ : ι → ℕ) (i : ι)
    (htop : isTop i = true → spec i = none) :
    (if isTop i = true then (κ i : ℝ) * (gam l - eps (lt i))
      else (κ i : ℝ) * (gam l - sig (lt i))) - (κ i : ℝ) * asmA_cost l eps (spec i) ≤
      (κ i : ℝ) * (gam l - rowRad l sig eps lt isTop spec i) := by sorry

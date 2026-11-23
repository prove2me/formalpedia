-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_frameM_idM
-- name    : Formalism.DworkPowerSeriesWeights.frameM_idM
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:58:40.81567+00:00
-- url     : https://prove2.me/theorems/7da675fb-a21a-4648-b09f-0c8f3a99112c
-- title:
--   Dwork Power Series Weights: frame M id M
-- statement:
--   The Dwork Power Series Weights construction uses the frame M id M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FJEval.lean#L139-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FJEval.lean#L139-L142

import Definitions.Def_Formalism_GaussJetBounds_FrameJetEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FJEval
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
variable {K : Type} [NormedField K] [CharZero K] {d N0 N1 : ℕ} [NeZero d]

theorem Formalism.DworkPowerSeriesWeights.frameM_idM (x : ZMod d × Fin N0 × Fin N0 → K) (z i : ZV d N0 N1) :
    frameM (N1 := N1) x z i =
      ∑ y, (idM : ZV d N0 N1 → ZV d N0 N1 → K) z y * frameM (N1 := N1) x y i := by sorry

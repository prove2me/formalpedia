-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_constantCoeff_linSub
-- name    : Formalism.DworkPowerSeriesWeights.constantCoeff_linSub
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T22:09:32.636964+00:00
-- url     : https://prove2.me/theorems/5362139d-f8f7-41d4-a403-f0cda5133761
-- title:
--   Dwork Power Series Weights: constant Coeff lin Sub
-- statement:
--   The Dwork Power Series Weights construction uses the constant Coeff lin Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FJEval.lean#L46-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FJEval.lean#L46-L48

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
variable {F K : Type} [NormedField F] [CharZero F] [NormedField K] [CharZero K] (φ : F →+* K)
  {d N0 N1 : ℕ} [NeZero d] {ι : Type} [Fintype ι]

theorem Formalism.DworkPowerSeriesWeights.constantCoeff_linSub (M : ZV d N0 N1 → ι → K) (z : ZV d N0 N1) :
    MvPowerSeries.constantCoeff (linSub M z) = 0 := by sorry

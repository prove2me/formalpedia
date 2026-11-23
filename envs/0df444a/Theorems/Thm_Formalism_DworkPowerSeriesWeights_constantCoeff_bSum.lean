-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_constantCoeff_bSum
-- name    : Formalism.DworkPowerSeriesWeights.constantCoeff_bSum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:00:26.938652+00:00
-- url     : https://prove2.me/theorems/90a104a9-b5dd-4c8c-b8b9-05d51159a4e7
-- title:
--   Dwork Power Series Weights: constant Coeff b Sum
-- statement:
--   The Dwork Power Series Weights construction uses the constant Coeff b Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FJEval.lean#L50-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FJEval.lean#L50-L58

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

theorem Formalism.DworkPowerSeriesWeights.constantCoeff_bSum (M : ZV d N0 N1 → ι → K) (be : MvPowerSeries (ZMod d) K)
    (hbe : MvPowerSeries.constantCoeff be = 0) :
    MvPowerSeries.constantCoeff (bSum M be) = 0 := by sorry

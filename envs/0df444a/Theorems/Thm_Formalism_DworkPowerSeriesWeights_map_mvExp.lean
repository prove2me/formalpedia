-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_map_mvExp
-- name    : Formalism.DworkPowerSeriesWeights.map_mvExp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:58:03.971394+00:00
-- url     : https://prove2.me/theorems/2ade8914-e356-4e7e-a374-6fecea396938
-- title:
--   Dwork Power Series Weights: map mv Exp
-- statement:
--   The Dwork Power Series Weights construction uses the map mv Exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FJEval.lean#L74-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FJEval.lean#L74-L80

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

theorem Formalism.DworkPowerSeriesWeights.map_mvExp (f : MvPowerSeries ι F) (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.map φ (mvExp f) = mvExp (MvPowerSeries.map φ f) := by sorry

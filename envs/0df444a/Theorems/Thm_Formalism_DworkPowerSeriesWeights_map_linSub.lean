-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_map_linSub
-- name    : Formalism.DworkPowerSeriesWeights.map_linSub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:03:18.527801+00:00
-- url     : https://prove2.me/theorems/5ab3751c-1632-4c27-964c-ed25882edea5
-- title:
--   Dwork Power Series Weights: map lin Sub
-- statement:
--   The Dwork Power Series Weights construction uses the map lin Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FJEval.lean#L60-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FJEval.lean#L60-L63

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

theorem Formalism.DworkPowerSeriesWeights.map_linSub (M : ZV d N0 N1 → ι → F) (z : ZV d N0 N1) :
    MvPowerSeries.map φ (linSub M z) = linSub (fun z i => φ (M z i)) z := by sorry

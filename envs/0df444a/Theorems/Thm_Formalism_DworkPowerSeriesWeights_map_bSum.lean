-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_map_bSum
-- name    : Formalism.DworkPowerSeriesWeights.map_bSum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:59:21.188974+00:00
-- url     : https://prove2.me/theorems/e5bc8210-1f9d-4939-8cfc-1f96e711e66a
-- title:
--   Dwork Power Series Weights: map b Sum
-- statement:
--   The Dwork Power Series Weights construction uses the map b Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FJEval.lean#L65-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FJEval.lean#L65-L72

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

theorem Formalism.DworkPowerSeriesWeights.map_bSum (M : ZV d N0 N1 → ι → F) (be : MvPowerSeries (ZMod d) F) :
    MvPowerSeries.map φ (bSum M be) = bSum (fun z i => φ (M z i)) (MvPowerSeries.map φ be) := by sorry

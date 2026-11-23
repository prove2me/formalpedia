-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_wtGe_mul_natCast
-- name    : Formalism.DworkPowerSeriesWeights.wtGe_mul_natCast
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:08:15.053515+00:00
-- url     : https://prove2.me/theorems/427dafc3-f82b-4ebd-88c7-0e5be65044df
-- title:
--   Dwork Power Series Weights: wt Ge mul nat Cast
-- statement:
--   The Dwork Power Series Weights construction uses the wt Ge mul nat Cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/PureCrossTermWeight.lean#L67-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/PureCrossTermWeight.lean#L67-L79

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_PureCrossTermWeight
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
universe u v w
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
variable {K : Type u} [NormedField K] {ι : Type v}
variable [IsUltrametricDist K]

theorem Formalism.DworkPowerSeriesWeights.wtGe_mul_natCast {pi : ℝ} (h0 : 0 < pi) {r : ι → ℝ} {wt : ℝ} {f : MvPowerSeries ι K}
    (hf : WtGe pi r wt f) {k : ℕ} (hk : ‖(k : K)‖ ≤ pi) :
    WtGe pi r (wt + 1) (f * (k : MvPowerSeries ι K)) := by sorry

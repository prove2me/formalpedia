-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_frob_two
-- name    : Formalism.DworkPowerSeriesWeights.frob_two
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:57:40.160304+00:00
-- url     : https://prove2.me/theorems/83c02b75-d290-438e-a0e2-384e44374eb9
-- title:
--   Dwork Power Series Weights: frob two
-- statement:
--   The Dwork Power Series Weights construction uses the frob two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/PureCrossTermWeight.lean#L81-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/PureCrossTermWeight.lean#L81-L98

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

theorem Formalism.DworkPowerSeriesWeights.frob_two {l : ℕ} (hl : l.Prime) (hpi0 : 0 < ‖(l : K)‖) {r : ι → ℝ} {wt : ℝ}
    {A B : MvPowerSeries ι K} (hA : WtGe ‖(l : K)‖ r wt A) (hB : WtGe ‖(l : K)‖ r wt B) :
    WtGe ‖(l : K)‖ r ((l : ℝ) * wt + 1) ((A + B) ^ l - A ^ l - B ^ l) := by sorry

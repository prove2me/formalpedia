-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_frob_sum
-- name    : Formalism.DworkPowerSeriesWeights.frob_sum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:57:51.409696+00:00
-- url     : https://prove2.me/theorems/5fdbf90f-fced-44c9-ac27-829d9a08c281
-- title:
--   Dwork Power Series Weights: frob sum
-- statement:
--   The Dwork Power Series Weights construction uses the frob sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/PureCrossTermWeight.lean#L100-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/PureCrossTermWeight.lean#L100-L117

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

theorem Formalism.DworkPowerSeriesWeights.frob_sum {l : ℕ} (hl : l.Prime) (hpi0 : 0 < ‖(l : K)‖) (hpi1 : ‖(l : K)‖ ≤ 1)
    {r : ι → ℝ} {wt : ℝ} {α : Type w} (s : Finset α) (A : α → MvPowerSeries ι K)
    (hA : ∀ i ∈ s, WtGe ‖(l : K)‖ r wt (A i)) :
    WtGe ‖(l : K)‖ r ((l : ℝ) * wt + 1) ((∑ i ∈ s, A i) ^ l - ∑ i ∈ s, A i ^ l) := by sorry

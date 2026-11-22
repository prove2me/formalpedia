-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_natCast_le_of_dvd
-- name    : Formalism.DworkPowerSeriesWeights.norm_natCast_le_of_dvd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:56:02.137109+00:00
-- url     : https://prove2.me/theorems/313818a2-904d-42af-8eb1-befab33811a8
-- title:
--   Dwork Power Series Weights: norm nat Cast le of dvd
-- statement:
--   The Dwork Power Series Weights construction uses the norm nat Cast le of dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/PureCrossTermWeight.lean#L59-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/PureCrossTermWeight.lean#L59-L65

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

theorem Formalism.DworkPowerSeriesWeights.norm_natCast_le_of_dvd {l k : ℕ} (h : l ∣ k) : ‖(k : K)‖ ≤ ‖(l : K)‖ := by sorry

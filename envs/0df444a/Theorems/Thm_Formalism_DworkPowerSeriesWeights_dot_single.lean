-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_dot_single
-- name    : Formalism.DworkPowerSeriesWeights.dot_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:00:09.922795+00:00
-- url     : https://prove2.me/theorems/a4e125f5-f2c3-4f36-b207-8a452a9281fb
-- title:
--   Dwork Power Series Weights: dot single
-- statement:
--   The Dwork Power Series Weights construction uses the dot single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/PureCrossTermWeight.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/PureCrossTermWeight.lean#L29-L31

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

theorem Formalism.DworkPowerSeriesWeights.dot_single (i : ι) (k : ℕ) (r : ι → ℝ) : dot (Finsupp.single i k) r = k * r i := by sorry

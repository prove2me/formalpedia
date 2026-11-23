-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_pow_pair_eq
-- name    : Formalism.DworkPowerSeriesWeights.pow_pair_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:59:27.079303+00:00
-- url     : https://prove2.me/theorems/c7ce3f65-9272-4225-95ac-e2cb275184b8
-- title:
--   Dwork Power Series Weights: pow pair eq
-- statement:
--   The Dwork Power Series Weights construction uses the pow pair eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/PureCrossTermWeight.lean#L47-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/PureCrossTermWeight.lean#L47-L55

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

theorem Formalism.DworkPowerSeriesWeights.pow_pair_eq [DecidableEq ι] (i j : ι) (x y : K) (a b : ℕ) :
    (MvPowerSeries.C x * MvPowerSeries.X i) ^ a * (MvPowerSeries.C y * MvPowerSeries.X j) ^ b =
      MvPowerSeries.monomial (Finsupp.single i a + Finsupp.single j b) (x ^ a * y ^ b) := by sorry

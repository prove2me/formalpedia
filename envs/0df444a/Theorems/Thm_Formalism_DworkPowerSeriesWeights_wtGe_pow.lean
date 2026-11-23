-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_wtGe_pow
-- name    : Formalism.DworkPowerSeriesWeights.wtGe_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:34:15.097301+00:00
-- url     : https://prove2.me/theorems/85be97a0-d92b-44df-8bdb-b6b16bd8057a
-- title:
--   Dwork Power Series Weights: wt Ge pow
-- statement:
--   The Dwork Power Series Weights construction uses the wt Ge pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SubstitutionWeightBound.lean#L81-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SubstitutionWeightBound.lean#L81-L89

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_WtGeProd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
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
variable {K : Type u} [NormedField K] {ι : Type v}
variable [IsUltrametricDist K]

theorem Formalism.DworkPowerSeriesWeights.wtGe_pow {pi : ℝ} (h0 : 0 < pi) {r : ι → ℝ} {wt : ℝ} {f : MvPowerSeries ι K}
    (hf : WtGe pi r wt f) (k : ℕ) : WtGe pi r (k * wt) (f ^ k) := by sorry

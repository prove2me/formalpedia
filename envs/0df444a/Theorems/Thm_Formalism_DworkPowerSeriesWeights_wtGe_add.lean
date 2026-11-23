-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_wtGe_add
-- name    : Formalism.DworkPowerSeriesWeights.wtGe_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:08:58.332057+00:00
-- url     : https://prove2.me/theorems/0c1c2704-3574-46cf-bbd4-08ef0aab99b1
-- title:
--   Dwork Power Series Weights: wt Ge add
-- statement:
--   The Dwork Power Series Weights construction uses the wt Ge add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SubstitutionWeightBound.lean#L43-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SubstitutionWeightBound.lean#L43-L50

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

theorem Formalism.DworkPowerSeriesWeights.wtGe_add {pi : ℝ} (h0 : 0 < pi) (h1 : pi ≤ 1) {r : ι → ℝ} {w1 w2 : ℝ}
    {f g : MvPowerSeries ι K} (hf : WtGe pi r w1 f) (hg : WtGe pi r w2 g) :
    WtGe pi r (min w1 w2) (f + g) := by sorry

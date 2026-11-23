-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_wtGe_mono
-- name    : Formalism.DworkPowerSeriesWeights.wtGe_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:15:58.564812+00:00
-- url     : https://prove2.me/theorems/cfce5356-4690-48be-b6f0-d92c0dc3357f
-- title:
--   Dwork Power Series Weights: wt Ge mono
-- statement:
--   The Dwork Power Series Weights construction uses the wt Ge mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SubstitutionWeightBound.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SubstitutionWeightBound.lean#L29-L31

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

theorem Formalism.DworkPowerSeriesWeights.wtGe_mono {pi : ℝ} (h0 : 0 < pi) (h1 : pi ≤ 1) {r : ι → ℝ} {w w' : ℝ} (hw : w' ≤ w)
    {f : MvPowerSeries ι K} (hf : WtGe pi r w f) : WtGe pi r w' f := by sorry

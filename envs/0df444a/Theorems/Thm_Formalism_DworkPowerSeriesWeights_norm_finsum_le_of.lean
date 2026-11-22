-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_finsum_le_of
-- name    : Formalism.DworkPowerSeriesWeights.norm_finsum_le_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:35:07.173735+00:00
-- url     : https://prove2.me/theorems/046262e6-0702-490d-9dd2-ae43b2d04dee
-- title:
--   Dwork Power Series Weights: norm finsum le of
-- statement:
--   The Dwork Power Series Weights construction uses the norm finsum le of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SubstitutionWeightBound.lean#L93-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SubstitutionWeightBound.lean#L93-L100

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

theorem Formalism.DworkPowerSeriesWeights.norm_finsum_le_of {K : Type u} [NormedField K] [IsUltrametricDist K] {α : Type v}
    {g : α → K} {C : ℝ} (hC : 0 ≤ C) (hg : ∀ n, ‖g n‖ ≤ C) : ‖∑ᶠ n, g n‖ ≤ C := by sorry

-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_radical_weight_monotone
-- name    : Formalism.DworkPowerSeriesWeights.radical_weight_monotone
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:09:34.266432+00:00
-- url     : https://prove2.me/theorems/a5a198e1-8f49-4419-8290-95fc8fd41562
-- title:
--   Dwork Power Series Weights: radical weight monotone
-- statement:
--   The Dwork Power Series Weights construction uses the radical weight monotone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SubstitutionWeightBound.lean#L120-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SubstitutionWeightBound.lean#L120-L125

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_WtGeProd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk29_wtGe_prod__77285e911b46

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

theorem Formalism.DworkPowerSeriesWeights.radical_weight_monotone : RadMono.{u, v} := by sorry

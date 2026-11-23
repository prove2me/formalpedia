-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_thmAWeyl_of
-- name    : Formalism.DworkPowerSeriesWeights.thmAWeyl_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:08:12.519379+00:00
-- url     : https://prove2.me/theorems/8d39d368-0452-458d-b4bf-7111792f6749
-- title:
--   Dwork Power Series Weights: thm AWeyl of
-- statement:
--   The Dwork Power Series Weights construction uses the thm AWeyl of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/CoefficientBoundMembership.lean#L94-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/CoefficientBoundMembership.lean#L94-L112

import Definitions.Def_Formalism_GaussJetBounds_StatementS
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_CoefficientBoundMembership
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
open Formalism Formalism.DworkPowerSeriesWeights
open MvPolynomial Formalism.IncomingBounds

theorem Formalism.DworkPowerSeriesWeights.thmAWeyl_of (hG : ThmAGauss) : ThmAWeyl := by sorry

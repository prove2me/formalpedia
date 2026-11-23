-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_lemmaSt_of
-- name    : Formalism.DworkPowerSeriesWeights.lemmaSt_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:58:49.231424+00:00
-- url     : https://prove2.me/theorems/1abfc31f-b65d-4ffa-a05a-5d24fc97da0d
-- title:
--   Dwork Power Series Weights: lemma St of
-- statement:
--   The Dwork Power Series Weights construction uses the lemma St of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffEvenDerivativeEqZero.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffEvenDerivativeEqZero.lean#L18-L21

import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_LogarithmWeightComparison
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffEvenDerivativeEqZero
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
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds MvPowerSeries

theorem Formalism.DworkPowerSeriesWeights.lemmaSt_of (hG : GenLogWeight.{u, 0}) (hB : LogBridges.{u}) : LemmaSt.{u} := by sorry

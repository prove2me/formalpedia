-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_lemmaS_of
-- name    : Formalism.DworkPowerSeriesWeights.lemmaS_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:58:56.840799+00:00
-- url     : https://prove2.me/theorems/d5f6e12c-2468-408f-85d3-6c9825ba241e
-- title:
--   Dwork Power Series Weights: lemma S of
-- statement:
--   The Dwork Power Series Weights construction uses the lemma S of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffEvenDerivativeEqZero.lean#L165-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffEvenDerivativeEqZero.lean#L165-L178

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

theorem Formalism.DworkPowerSeriesWeights.lemmaS_of (hGW : GenLogWeight.{u, 0}) (hGI : GenLogInverse.{u, 0}) (hB : LogBridges.{u})
    (hSW : SubstWt.{u, 0, 0}) (hX : ExpDeInv.{u}) (hQ : Quant.{u}) (hLS : LogStep.{u, 0})
    (hBE : BinomExtract.{u}) : LemmaS.{u} := by sorry

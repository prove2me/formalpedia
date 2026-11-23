-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmS_cc_subst
-- name    : Formalism.DworkPowerSeriesWeights.asmS_cc_subst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:59:29.878807+00:00
-- url     : https://prove2.me/theorems/7e4d1267-555c-4788-85e4-1a8c56687181
-- title:
--   Dwork Power Series Weights: asm S cc subst
-- statement:
--   The Dwork Power Series Weights construction uses the asm S cc subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffEvenDerivativeEqZero.lean#L58-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffEvenDerivativeEqZero.lean#L58-L76

import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_LogarithmWeightComparison
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffEvenDerivativeEqZero
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

theorem Formalism.DworkPowerSeriesWeights.asmS_cc_subst {K : Type u} [Field K] {d : ℕ} [NeZero d] {be : MvPowerSeries (ZMod d) K}
    (hbe0 : constantCoeff be = 0) (a : ZMod d → MvPowerSeries (V2 d) K)
    (ha : ∀ s, constantCoeff (a s) = 0) : constantCoeff (subst a be) = 0 := by sorry

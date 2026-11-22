-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_C_mul_right
-- name    : Formalism.DworkPowerSeriesWeights.jetPair_C_mul_right
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T22:06:29.101484+00:00
-- url     : https://prove2.me/theorems/276a2756-1597-4416-bf4e-fa445e44fe42
-- title:
--   Dwork Power Series Weights: jet Pair C mul right
-- statement:
--   The Dwork Power Series Weights construction uses the jet Pair C mul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffAevalLinP.lean#L64-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffAevalLinP.lean#L64-L68

import Definitions.Def_Formalism_GaussJetBounds_StatementJ
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
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
open Formalism.IncomingBounds
variable {K : Type u} [Field K] {ι : Type}

theorem Formalism.DworkPowerSeriesWeights.jetPair_C_mul_right (c : K) (P : MvPolynomial ι K) (F : MvPowerSeries ι K) :
    jetPair P (MvPowerSeries.C c * F) = c * jetPair P F := by sorry

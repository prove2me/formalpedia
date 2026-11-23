-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_constantCoeff_aeval_linP
-- name    : Formalism.DworkPowerSeriesWeights.constantCoeff_aeval_linP
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:57:10.725347+00:00
-- url     : https://prove2.me/theorems/e0410dfe-f772-4dae-9eab-b7759aa3dee5
-- title:
--   Dwork Power Series Weights: constant Coeff aeval lin P
-- statement:
--   The Dwork Power Series Weights construction uses the constant Coeff aeval lin P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffAevalLinP.lean#L170-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffAevalLinP.lean#L170-L178

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
variable {K : Type u} [Field K] {ι ι' : Type} [Fintype ι] [Fintype ι']

theorem Formalism.DworkPowerSeriesWeights.constantCoeff_aeval_linP (A : ι → ι' → K) (G : MvPolynomial ι' K) :
    MvPolynomial.constantCoeff (MvPolynomial.aeval (linP A) G) = MvPolynomial.constantCoeff G := by sorry

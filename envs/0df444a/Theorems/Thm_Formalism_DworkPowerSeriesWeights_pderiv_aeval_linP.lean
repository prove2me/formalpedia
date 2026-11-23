-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_pderiv_aeval_linP
-- name    : Formalism.DworkPowerSeriesWeights.pderiv_aeval_linP
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:02:39.120172+00:00
-- url     : https://prove2.me/theorems/e3f95d38-70cc-4981-a307-2c2eec41b3b8
-- title:
--   Dwork Power Series Weights: pderiv aeval lin P
-- statement:
--   The Dwork Power Series Weights construction uses the pderiv aeval lin P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffAevalLinP.lean#L138-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffAevalLinP.lean#L138-L165

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

theorem Formalism.DworkPowerSeriesWeights.pderiv_aeval_linP (A : ι → ι' → K) (i : ι) (G : MvPolynomial ι' K) :
    MvPolynomial.pderiv i (MvPolynomial.aeval (linP A) G) =
      ∑ j, MvPolynomial.C (A i j) * MvPolynomial.aeval (linP A) (MvPolynomial.pderiv j G) := by sorry

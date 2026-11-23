-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_poly
-- name    : Formalism.DworkPowerSeriesWeights.jetPair_poly
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:59:17.363663+00:00
-- url     : https://prove2.me/theorems/2ccb42d6-ed2b-45c2-b510-159ec53cb02e
-- title:
--   Dwork Power Series Weights: jet Pair poly
-- statement:
--   The Dwork Power Series Weights construction uses the jet Pair poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffAevalLinP.lean#L188-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffAevalLinP.lean#L188-L223

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

theorem Formalism.DworkPowerSeriesWeights.jetPair_poly (A : ι → ι' → K) (P : MvPolynomial ι K) :
    ∀ G : MvPolynomial ι' K,
      jetPair P ((MvPolynomial.aeval (linP A) G : MvPolynomial ι K) : MvPowerSeries ι K) =
        jetPair (MvPolynomial.aeval (linP' A) P) (G : MvPowerSeries ι' K) := by sorry

-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_monomial_right
-- name    : Formalism.DworkPowerSeriesWeights.jetPair_monomial_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:59:43.994732+00:00
-- url     : https://prove2.me/theorems/101332d0-d989-4215-b96d-10a58a6eb889
-- title:
--   Dwork Power Series Weights: jet Pair monomial right
-- statement:
--   The Dwork Power Series Weights construction uses the jet Pair monomial right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffAevalLinP.lean#L225-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffAevalLinP.lean#L225-L234

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

theorem Formalism.DworkPowerSeriesWeights.jetPair_monomial_right (P : MvPolynomial ι' K) (μ : ι' →₀ ℕ) :
    jetPair P ((MvPolynomial.monomial μ (1 : K) : MvPolynomial ι' K) : MvPowerSeries ι' K) =
      MvPolynomial.coeff μ P * ((mfact μ : ℕ) : K) := by sorry

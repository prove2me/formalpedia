-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_eq_sum
-- name    : Formalism.DworkPowerSeriesWeights.jetPair_eq_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:04:51.050116+00:00
-- url     : https://prove2.me/theorems/711750bb-81a1-4876-849b-a9ce128d792f
-- title:
--   Dwork Power Series Weights: jet Pair eq sum
-- statement:
--   The Dwork Power Series Weights construction uses the jet Pair eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffAevalLinP.lean#L17-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffAevalLinP.lean#L17-L26

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

theorem Formalism.DworkPowerSeriesWeights.jetPair_eq_sum (P : MvPolynomial ι K) (F : MvPowerSeries ι K) (S : Finset (ι →₀ ℕ))
    (hS : P.support ⊆ S) :
    jetPair P F =
      ∑ κ ∈ S, MvPolynomial.coeff κ P * ((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ F := by sorry

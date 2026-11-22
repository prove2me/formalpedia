-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_subst_mvExp
-- name    : Formalism.DworkPowerSeriesWeights.subst_mvExp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:05:34.700966+00:00
-- url     : https://prove2.me/theorems/df93a798-4c02-4f28-8dd6-7296ef2f5244
-- title:
--   Dwork Power Series Weights: subst mv Exp
-- statement:
--   The Dwork Power Series Weights construction uses the subst mv Exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffAevalLinP.lean#L310-L318
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffAevalLinP.lean#L310-L318

import Definitions.Def_Formalism_GaussJetBounds_StatementJ
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs

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

theorem Formalism.DworkPowerSeriesWeights.subst_mvExp {K : Type u} [NormedField K] [CharZero K] {ι ι' : Type} {a : ι' → MvPowerSeries ι K}
    (hs : MvPowerSeries.HasSubst a) (f : MvPowerSeries ι' K)
    (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.subst a (mvExp f) = mvExp (MvPowerSeries.subst a f) := by sorry

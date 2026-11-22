-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_subst_linSub
-- name    : Formalism.DworkPowerSeriesWeights.subst_linSub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:05:32.335928+00:00
-- url     : https://prove2.me/theorems/b2050a55-5587-435f-863a-44bd99295061
-- title:
--   Dwork Power Series Weights: subst lin Sub
-- statement:
--   The Dwork Power Series Weights construction uses the subst lin Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffAevalLinP.lean#L284-L308
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffAevalLinP.lean#L284-L308

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

theorem Formalism.DworkPowerSeriesWeights.subst_linSub {K : Type u} [Field K] {d N0 N1 : ℕ} {ι ι' : Type} [Fintype ι] [Fintype ι']
    (M : ZV d N0 N1 → ι' → K) (A : ι → ι' → K) (Mg : ZV d N0 N1 → ι → K)
    (h : ∀ z i, Mg z i = ∑ y, M z y * A i y) (z : ZV d N0 N1) :
    MvPowerSeries.subst
        (fun j : ι' => (∑ i : ι, MvPowerSeries.C (A i j) * MvPowerSeries.X i : MvPowerSeries ι K))
        (linSub M z) = linSub Mg z := by sorry

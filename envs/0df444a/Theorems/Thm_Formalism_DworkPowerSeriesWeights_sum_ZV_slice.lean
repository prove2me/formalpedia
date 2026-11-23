-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_sum_ZV_slice
-- name    : Formalism.DworkPowerSeriesWeights.sum_ZV_slice
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:05:07.197149+00:00
-- url     : https://prove2.me/theorems/285bca07-37e3-4a19-b0c7-354c445197f1
-- title:
--   Dwork Power Series Weights: sum ZV slice
-- statement:
--   The Dwork Power Series Weights construction uses the sum ZV slice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffAevalLinP.lean#L320-L332
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffAevalLinP.lean#L320-L332

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

theorem Formalism.DworkPowerSeriesWeights.sum_ZV_slice {d N0 N1 : ℕ} [NeZero d] {M : Type*} [AddCommMonoid M] (s : ZMod d)
    (b : Fin N1) (f : ZV d N0 N1 → M) (hf : ∀ y, ¬ (y.1 = s ∧ y.2.2 = b) → f y = 0) :
    ∑ y, f y = ∑ k, f (s, k, b) := by sorry

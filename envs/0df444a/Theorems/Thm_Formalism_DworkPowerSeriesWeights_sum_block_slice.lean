-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_sum_block_slice
-- name    : Formalism.DworkPowerSeriesWeights.sum_block_slice
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:53:28.812433+00:00
-- url     : https://prove2.me/theorems/c8ba65ab-d2d5-4584-879f-0202ce4b706a
-- title:
--   Dwork Power Series Weights: sum block slice
-- statement:
--   The Dwork Power Series Weights construction uses the sum block slice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FirstRowMinorDegreeLeOne.lean#L246-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FirstRowMinorDegreeLeOne.lean#L246-L262

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormDetLeOneOfEntries
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_MfactEqProdUniv
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FirstRowMinorDegreeLeOne
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
open MvPolynomial

theorem Formalism.DworkPowerSeriesWeights.sum_block_slice {T : Type} [Fintype T] [DecidableEq T] {N0 N1 : ℕ} {M : Type*}
    [AddCommMonoid M] (s : T) (b : Fin N1) (f : T × Fin N0 × Fin N1 → M)
    (hf : ∀ y, ¬ (y.1 = s ∧ y.2.2 = b) → f y = 0) :
    ∑ y, f y = ∑ k, f (s, k, b) := by sorry

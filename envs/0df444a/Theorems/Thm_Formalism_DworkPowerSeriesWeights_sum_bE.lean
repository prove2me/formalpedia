-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_sum_bE
-- name    : Formalism.DworkPowerSeriesWeights.sum_bE
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:52:13.370588+00:00
-- url     : https://prove2.me/theorems/df9a8c13-f825-4f21-bc44-266fce037326
-- title:
--   Dwork Power Series Weights: sum b E
-- statement:
--   The Dwork Power Series Weights construction uses the sum b E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FirstRowMinorDegreeLeOne.lean#L330-L332
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FirstRowMinorDegreeLeOne.lean#L330-L332

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
variable {K : Type u} [Field K] {H : Type} {N0 : ℕ}

theorem Formalism.DworkPowerSeriesWeights.sum_bE [Fintype H] {N1 : ℕ} {M : Type*} [AddCommMonoid M]
    (f : Bool × H × Fin N0 × Fin N1 → M) : ∑ y, f y = ∑ w, f (bE H N0 N1 w) := by sorry

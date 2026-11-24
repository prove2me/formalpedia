-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_injective_apply_prodMk_of_injective
-- name    : Formalism.DworkPowerSeriesWeights.injective_apply_prodMk_of_injective
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:53:41.342936+00:00
-- url     : https://prove2.me/theorems/d8750322-fc40-448e-a38a-bd48d9238708
-- title:
--   Dwork Power Series Weights: injective apply prod Mk of injective
-- statement:
--   The Dwork Power Series Weights construction uses the injective apply prod Mk of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FirstRowMinorDegreeLeOne.lean#L37-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FirstRowMinorDegreeLeOne.lean#L37-L39

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
variable {R : Type u} [CommRing R] {T σ ρ : Type}

theorem Formalism.DworkPowerSeriesWeights.injective_apply_prodMk_of_injective (e : T × σ → ρ) (he : Function.Injective e) (t : T) :
    Function.Injective (fun y : σ => e (t, y)) := by sorry

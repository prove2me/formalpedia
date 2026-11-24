-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_slice_prod
-- name    : Formalism.DworkPowerSeriesWeights.slice_prod
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:51:55.887741+00:00
-- url     : https://prove2.me/theorems/c9251b8e-7459-402d-91f3-fdaed35d4d39
-- title:
--   Dwork Power Series Weights: slice prod
-- statement:
--   The Dwork Power Series Weights construction uses the slice prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FirstRowMinorDegreeLeOne.lean#L55-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FirstRowMinorDegreeLeOne.lean#L55-L87

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

theorem Formalism.DworkPowerSeriesWeights.slice_prod (e : T × σ → ρ) (he : Function.Injective e) (Q : T → MvPolynomial σ R)
    (s : Finset T) :
    ∀ κ ∈ (∏ t ∈ s, rename (fun y => e (t, y)) (Q t)).support,
      (∀ t ∈ s, bSlice e he t κ ∈ (Q t).support) ∧ ∀ t, t ∉ s → bSlice e he t κ = 0 := by sorry

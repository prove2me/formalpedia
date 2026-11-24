-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_bT_mul_bM
-- name    : Formalism.DworkPowerSeriesWeights.bT_mul_bM
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:53:55.117973+00:00
-- url     : https://prove2.me/theorems/cdd24206-0778-4a23-88c5-c5ab692559c3
-- title:
--   Dwork Power Series Weights: b T mul b M
-- statement:
--   The Dwork Power Series Weights construction uses the b T mul b M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FirstRowMinorDegreeLeOne.lean#L302-L310
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FirstRowMinorDegreeLeOne.lean#L302-L310

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

theorem Formalism.DworkPowerSeriesWeights.bT_mul_bM (x : Bool × H → Matrix (Fin N0) (Fin N0) K) (hx : ∀ τ, (x τ).det ≠ 0)
    (τ : Bool × H) : bT x τ * bM x τ = x τ := by sorry

-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_bSlice_mapDomain_ne
-- name    : Formalism.DworkPowerSeriesWeights.bSlice_mapDomain_ne
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:53:03.029855+00:00
-- url     : https://prove2.me/theorems/dfe18071-1cf6-4cf8-9c3c-66602adcb357
-- title:
--   Dwork Power Series Weights: b Slice map Domain ne
-- statement:
--   The Dwork Power Series Weights construction uses the b Slice map Domain ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FirstRowMinorDegreeLeOne.lean#L47-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FirstRowMinorDegreeLeOne.lean#L47-L53

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

theorem Formalism.DworkPowerSeriesWeights.bSlice_mapDomain_ne (e : T × σ → ρ) (he : Function.Injective e) {t t' : T} (h : t ≠ t')
    (u : σ →₀ ℕ) : bSlice e he t (u.mapDomain (fun y => e (t', y))) = 0 := by sorry

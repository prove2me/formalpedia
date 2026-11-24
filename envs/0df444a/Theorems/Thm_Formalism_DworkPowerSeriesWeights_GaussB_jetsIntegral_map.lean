-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_GaussB_jetsIntegral_map
-- name    : Formalism.DworkPowerSeriesWeights.GaussB.jetsIntegral_map
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:03:54.156746+00:00
-- url     : https://prove2.me/theorems/b9942d3b-90b7-40ee-9692-a893986ace0b
-- title:
--   Gauss B: jets Integral map
-- statement:
--   The Gauss B construction uses the jets Integral map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/GaussB.lean#L60-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/GaussB.lean#L60-L65

import Definitions.Def_Formalism_GaussJetBounds_StatementY
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FirstRowMinorDegreeLeOne
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_GField
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FJEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Labels
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_GaussB
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
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.DworkPowerSeriesWeights.GaussB

theorem Formalism.DworkPowerSeriesWeights.GaussB.jetsIntegral_map {F K : Type} [NormedField F] [NormedField K] (φ : F →+* K)
    (hφ : ∀ z, ‖φ z‖ = ‖z‖) {ι : Type} {sg : MvPowerSeries ι F} (h : JetsIntegral sg) :
    JetsIntegral (MvPowerSeries.map φ sg) := by sorry

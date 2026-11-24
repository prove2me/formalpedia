-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_GaussB_norm_det_generic
-- name    : Formalism.DworkPowerSeriesWeights.GaussB.norm_det_generic
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:04:00.209419+00:00
-- url     : https://prove2.me/theorems/ab39fd94-365c-40e3-a3ac-1328ec181590
-- title:
--   Gauss B: norm det generic
-- statement:
--   The Gauss B construction uses the norm det generic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/GaussB.lean#L14-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/GaussB.lean#L14-L37

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

theorem Formalism.DworkPowerSeriesWeights.GaussB.norm_det_generic {K : Type} [NormedField K] {T : Type} {N0 : ℕ} (p : ℕ) [Fact p.Prime]
    (Y : T × Fin N0 × Fin N0 → K) (hY : IsGeneric p Y) (τ : T) :
    ‖(Matrix.of fun i a : Fin N0 => Y (τ, i, a)).det‖ = 1 := by sorry

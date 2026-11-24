-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_GaussB_map_expo
-- name    : Formalism.DworkPowerSeriesWeights.GaussB.map_expo
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:05:06.407329+00:00
-- url     : https://prove2.me/theorems/8e3daa37-2a1c-478b-a762-a867ebe79d5d
-- title:
--   Gauss B: map expo
-- statement:
--   The Gauss B construction uses the map expo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/GaussB.lean#L49-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/GaussB.lean#L49-L58

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

theorem Formalism.DworkPowerSeriesWeights.GaussB.map_expo {F K : Type} [Field F] [Field K] (φ : F →+* K) {H : Type} [Fintype H] {N0 N1 : ℕ}
    (S : F) (u : H → F) :
    MvPowerSeries.map φ ((-S) • ∑ t : H, ∑ ab : Fin N0 × Fin N1, MvPowerSeries.C (u t) *
      MvPowerSeries.X ((false, t), ab.1, ab.2) * MvPowerSeries.X ((true, t), ab.1, ab.2) :
        MvPowerSeries ((Bool × H) × Fin N0 × Fin N1) F) =
      (-(φ S)) • ∑ t : H, ∑ ab : Fin N0 × Fin N1, MvPowerSeries.C (φ (u t)) *
        MvPowerSeries.X ((false, t), ab.1, ab.2) * MvPowerSeries.X ((true, t), ab.1, ab.2) := by sorry

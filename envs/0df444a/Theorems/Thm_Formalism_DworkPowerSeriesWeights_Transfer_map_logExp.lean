-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_Transfer_map_logExp
-- name    : Formalism.DworkPowerSeriesWeights.Transfer.map_logExp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:53:22.650004+00:00
-- url     : https://prove2.me/theorems/32dc1ee2-ac71-43b5-bc9e-4c987fdf9699
-- title:
--   Transfer: map log Exp
-- statement:
--   The Transfer construction uses the map log Exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/Transfer.lean#L148-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/Transfer.lean#L148-L156

import Definitions.Def_Formalism_GaussJetBounds_FrameJetEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Transfer
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
open Formalism.IncomingBounds MvPowerSeries
open Formalism.DworkPowerSeriesWeights.Transfer
variable {F K : Type} [NormedField F] [CharZero F] [NormedField K] [CharZero K] (φ : F →+* K)

theorem Formalism.DworkPowerSeriesWeights.Transfer.map_logExp {d : ℕ} [NeZero d] (l : ℕ) {f : MvPowerSeries (V2 d) F}
    (h : constantCoeff f = 0) :
    map φ (subst (letterLog (K := F) l) (mvExp f)) =
      subst (letterLog (K := K) l) (mvExp (map φ f)) := by sorry

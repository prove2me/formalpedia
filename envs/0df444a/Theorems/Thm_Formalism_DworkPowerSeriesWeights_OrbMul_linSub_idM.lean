-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_OrbMul_linSub_idM
-- name    : Formalism.DworkPowerSeriesWeights.OrbMul.linSub_idM
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:59:02.478199+00:00
-- url     : https://prove2.me/theorems/bce05640-061d-4a2b-a498-31c291c24925
-- title:
--   Orb Mul: lin Sub id M
-- statement:
--   The Orb Mul construction uses the lin Sub id M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/OrbMul.lean#L87-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/OrbMul.lean#L87-L91

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementW
import Definitions.Def_Formalism_GaussJetBounds_ThmAGauss
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneGauss
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OrbMul
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
open Formalism.IncomingBounds
open Formalism.DworkPowerSeriesWeights.OrbMul

theorem Formalism.DworkPowerSeriesWeights.OrbMul.linSub_idM {K : Type} [Field K] {d N0 N1 : ℕ} [NeZero d] (x : ZV d N0 N1) :
    linSub (idM : ZV d N0 N1 → ZV d N0 N1 → K) x = MvPowerSeries.X x := by sorry

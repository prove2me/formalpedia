-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_OrbMul_thetaZ_eq
-- name    : Formalism.DworkPowerSeriesWeights.OrbMul.thetaZ_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:53:52.146266+00:00
-- url     : https://prove2.me/theorems/15278c43-b569-4115-94d7-fe2d26c8ef37
-- title:
--   Orb Mul: theta Z eq
-- statement:
--   The Orb Mul construction uses the theta Z eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/OrbMul.lean#L93-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/OrbMul.lean#L93-L101

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

theorem Formalism.DworkPowerSeriesWeights.OrbMul.thetaZ_eq {K : Type} [NormedField K] [CharZero K] {d N0 N1 : ℕ} [NeZero d]
    (g : ZV d N0 N1 → MvPowerSeries (ZV d N0 N1) K) (U : MvPowerSeries (ZV d N0 N1) K) (ε : K)
    (be : MvPowerSeries (ZMod d) K) :
    thetaZ g U ε be = MvPowerSeries.subst g U *
      mvExp (ε • bSum (idM : ZV d N0 N1 → ZV d N0 N1 → K) be) := by sorry

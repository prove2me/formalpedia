-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_subst_zeroPt
-- name    : Formalism.L2.FormalSeriesBounds.VP.subst_zeroPt
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:15:56.786786+00:00
-- url     : https://prove2.me/theorems/d20586b6-3091-4688-a405-215ec39dd961
-- title:
--   VP: subst zero Pt
-- statement:
--   The VP construction uses the subst zero Pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ValuationEqPairOfUnitGerm.lean#L17-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ValuationEqPairOfUnitGerm.lean#L17-L29

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_PullbackLogCoordsEvalZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqPairOfUnitGerm
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst

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
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open Formalism.L2.FormalSeriesBounds.VP
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem Formalism.L2.FormalSeriesBounds.VP.subst_zeroPt {σ τ : Type} [Finite σ] (f : MvPowerSeries σ C) :
    MvPowerSeries.subst (fun _ : σ => (0 : MvPowerSeries τ C)) f = MvPowerSeries.C (MvPowerSeries.constantCoeff f) := by sorry

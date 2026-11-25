-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_l_add
-- name    : Formalism.L2.FormalSeriesBounds.VP.l_add
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:21:30.598876+00:00
-- url     : https://prove2.me/theorems/a72f93a4-febb-5f75-987d-a999ecf67ac2
-- title:
--   VP: l add
-- statement:
--   The VP construction uses the l add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ValuationEqPairOfUnitGerm.lean#L70-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ValuationEqPairOfUnitGerm.lean#L70-L83

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_PullbackLogCoordsEvalZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqPairOfUnitGerm
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
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
variable (Y : FBChart C V O dd)

theorem Formalism.L2.FormalSeriesBounds.VP.l_add (m : Fin dd) :
    MvPowerSeries.subst (fun k => Y.B.G.F k) (l Y m) =
      MvPowerSeries.subst (fun k : Fin dd => (MvPowerSeries.X ((0 : Fin 2), k) : PS C 2 dd)) (l Y m) +
        MvPowerSeries.subst (fun k : Fin dd => (MvPowerSeries.X ((1 : Fin 2), k) : PS C 2 dd)) (l Y m) := by sorry

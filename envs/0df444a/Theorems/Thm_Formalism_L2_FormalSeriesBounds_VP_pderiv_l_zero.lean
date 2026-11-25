-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_pderiv_l_zero
-- name    : Formalism.L2.FormalSeriesBounds.VP.pderiv_l_zero
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:12:28.868676+00:00
-- url     : https://prove2.me/theorems/214d2c44-c41c-50a5-95a8-dc39d3bcf0d3
-- title:
--   VP: pderiv l zero
-- statement:
--   The VP construction uses the pderiv l zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ValuationEqPairOfUnitGerm.lean#L128-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ValuationEqPairOfUnitGerm.lean#L128-L140

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_PullbackLogCoordsEvalZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqPairOfUnitGerm
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

theorem Formalism.L2.FormalSeriesBounds.VP.pderiv_l_zero (m i : Fin dd) :
    MvPowerSeries.constantCoeff (MvPowerSeries.pderiv C i (l Y m)) = if m = i then 1 else 0 := by sorry

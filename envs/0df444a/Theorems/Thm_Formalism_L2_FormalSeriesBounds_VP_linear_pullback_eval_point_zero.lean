-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_linear_pullback_eval_point_zero
-- name    : Formalism.L2.FormalSeriesBounds.VP.linear_pullback_eval_point_zero
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:20:48.645842+00:00
-- url     : https://prove2.me/theorems/3b1b6cd8-6fb3-5356-b678-da314b0fd723
-- title:
--   VP: linear pullback eval point zero
-- statement:
--   The VP construction uses the linear pullback eval point zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieValG.lean#L38-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieValG.lean#L38-L50

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqPairOfUnitGerm
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValG
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
  {Var : Type} [Fintype Var] {n : ℕ}
variable (Y : FBChart C V O dd) (M : Var → Fin n × Fin dd → C)

theorem Formalism.L2.FormalSeriesBounds.VP.linear_pullback_eval_point_zero (b : Fin n) (G : PS C 2 dd) :
    linPull Y M (ev (n := n) ![pt C dd b, 0] G) =
      MvPowerSeries.subst (linS (colLin M b)) (MvPowerSeries.subst (exZero Y) G) := by sorry

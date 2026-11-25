-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_mapAt_act
-- name    : Formalism.L2.FormalSeriesBounds.VP.mapAt_act
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:38:28.641087+00:00
-- url     : https://prove2.me/theorems/c59ce8a7-a9e8-42f7-9ba4-e2059fc17c45
-- title:
--   VP: map At act
-- statement:
--   The VP construction uses the map At act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieValCr.lean#L67-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieValCr.lean#L67-L88

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValBr
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValCr
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_GoodPt_act

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
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {τ τ' : Type}
variable (Y : FBChart C V O dd)

theorem Formalism.L2.FormalSeriesBounds.VP.mapAt_act {ε : Pt C 1 dd} (hε : ∀ i, MvPowerSeries.constantCoeff (ε i) = 0) (x : O)
    (hc : comp1 ε (Y.B.A.act x) = comp1 (Y.B.A.act x) ε) {a : Fin dd → MvPowerSeries τ C}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) :
    mapAt ε (actAt Y x a) = actAt Y x (mapAt ε a) := by sorry

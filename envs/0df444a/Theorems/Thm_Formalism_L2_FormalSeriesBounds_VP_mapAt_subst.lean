-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_mapAt_subst
-- name    : Formalism.L2.FormalSeriesBounds.VP.mapAt_subst
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:40:25.762963+00:00
-- url     : https://prove2.me/theorems/9b2be178-0e70-4b4e-82a8-bc44690fd0a5
-- title:
--   VP: map At subst
-- statement:
--   The VP construction uses the map At subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieValCr.lean#L48-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieValCr.lean#L48-L55

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValBr
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValCr
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
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {τ τ' : Type}

theorem Formalism.L2.FormalSeriesBounds.VP.mapAt_subst [Finite τ] {A : τ → MvPowerSeries τ' C} (hA : ∀ s, MvPowerSeries.constantCoeff (A s) = 0)
    (ε : Pt C 1 dd) {u : Fin dd → MvPowerSeries τ C} (hu : ∀ i, MvPowerSeries.constantCoeff (u i) = 0) (i : Fin dd) :
    MvPowerSeries.subst A (mapAt ε u i) = mapAt ε (fun i => MvPowerSeries.subst A (u i)) i := by sorry

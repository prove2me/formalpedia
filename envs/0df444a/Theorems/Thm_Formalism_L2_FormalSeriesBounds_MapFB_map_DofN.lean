-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_MapFB_map_DofN
-- name    : Formalism.L2.FormalSeriesBounds.MapFB.map_DofN
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:47:49.451811+00:00
-- url     : https://prove2.me/theorems/fadbf484-6613-49a9-a1ad-31446072241f
-- title:
--   Map FB: map Dof N
-- statement:
--   The Map FB construction uses the map Dof N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePNabMapSt.lean#L23-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePNabMapSt.lean#L23-L28

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieDesc
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePGaugeMapSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePNabMapSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.MapFB
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
variable {K C : Type} [Field K] [Field C] (φ : K →+* C) {d : ℕ}

theorem Formalism.L2.FormalSeriesBounds.MapFB.map_DofN (F : Fin d → PS K 2 d) {n : ℕ} (b : Fin n) (u : Fin d → K) (f : PS K n d) :
    MvPowerSeries.map φ (DofN F b u f) =
      DofN (fun j => MvPowerSeries.map φ (F j)) b (fun i => φ (u i)) (MvPowerSeries.map φ f) := by sorry

-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_MapFB_map_pderiv
-- name    : Formalism.L2.FormalSeriesBounds.MapFB.map_pderiv
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:48:08.139977+00:00
-- url     : https://prove2.me/theorems/bc653e9e-bbde-49f5-bc3d-1e5698cda7eb
-- title:
--   Map FB: map pderiv
-- statement:
--   The Map FB construction uses the map pderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePNabMapSt.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePNabMapSt.lean#L18-L21

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

theorem Formalism.L2.FormalSeriesBounds.MapFB.map_pderiv {σ : Type} (x : σ) (f : MvPowerSeries σ K) :
    MvPowerSeries.map φ (pderiv K x f) = pderiv C x (MvPowerSeries.map φ f) := by sorry

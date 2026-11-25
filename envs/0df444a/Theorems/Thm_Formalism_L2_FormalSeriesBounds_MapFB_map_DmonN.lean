-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_MapFB_map_DmonN
-- name    : Formalism.L2.FormalSeriesBounds.MapFB.map_DmonN
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:48:09.246732+00:00
-- url     : https://prove2.me/theorems/b9389152-9ece-4be0-be54-628bcb7904fd
-- title:
--   Map FB: map Dmon N
-- statement:
--   The Map FB construction uses the map Dmon N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePNabMapSt.lean#L37-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePNabMapSt.lean#L37-L44

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

theorem Formalism.L2.FormalSeriesBounds.MapFB.map_DmonN (F : Fin d → PS K 2 d) {n : ℕ} {ι : Type} [Fintype ι] (cp : ι → Fin n)
    (u : ι → Fin d → K) (m : ι →₀ ℕ) (f : PS K n d) :
    MvPowerSeries.map φ (DmonN F cp u m f) =
      DmonN (fun j => MvPowerSeries.map φ (F j)) cp (fun l i => φ (u l i)) m (MvPowerSeries.map φ f) := by sorry

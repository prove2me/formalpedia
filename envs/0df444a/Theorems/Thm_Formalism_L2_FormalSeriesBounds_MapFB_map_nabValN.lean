-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_MapFB_map_nabValN
-- name    : Formalism.L2.FormalSeriesBounds.MapFB.map_nabValN
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:47:57.501724+00:00
-- url     : https://prove2.me/theorems/e3c82b3c-a018-4063-89ee-21654e094824
-- title:
--   Map FB: map nab Val N
-- statement:
--   The Map FB construction uses the map nab Val N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePNabMapSt.lean#L61-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePNabMapSt.lean#L61-L95

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

theorem Formalism.L2.FormalSeriesBounds.MapFB.map_nabValN [Algebra ℚ K] [Algebra ℚ C] {O : Type} [CommRing O] [StarRing O]
    (B : FB K d O) (B' : FB C d O) (hF : ∀ j, B'.G.F j = MvPowerSeries.map φ (B.G.F j))
    (hA : ∀ a j, B'.A.act a j = MvPowerSeries.map φ (B.A.act a j)) (h : PS K 2 d)
    (hh : constantCoeff h = 0) (w0 : O) (m : ℕ) {n : ℕ} (f : PS K n d) {ι : Type} [Fintype ι]
    (cp : ι → Fin n) (u : ι → Fin d → K) (P : MvPolynomial ι K) :
    nabValN B' C (MvPowerSeries.map φ h) w0 m (MvPowerSeries.map φ f) cp (fun l i => φ (u l i))
        (MvPolynomial.map φ P) = φ (nabValN B K h w0 m f cp u P) := by sorry

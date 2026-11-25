-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_MapFB_constantCoeff_eval_pair
-- name    : Formalism.L2.FormalSeriesBounds.MapFB.constantCoeff_eval_pair
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:35:00.750819+00:00
-- url     : https://prove2.me/theorems/94b9538b-2c2b-47e7-9e55-9b884a28b702
-- title:
--   Map FB: constant Coeff eval pair
-- statement:
--   The Map FB construction uses the constant Coeff eval pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePGaugeMapSt.lean#L33-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePGaugeMapSt.lean#L33-L35

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePFBMapSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePGaugeMapSt
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {R : Type} [CommRing R] {d : ℕ}

theorem Formalism.L2.FormalSeriesBounds.MapFB.constantCoeff_eval_pair {n : ℕ} (a b : Pt R n d) (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) (f : PS R 2 d) :
    constantCoeff (ev ![a, b] f) = constantCoeff f := by sorry

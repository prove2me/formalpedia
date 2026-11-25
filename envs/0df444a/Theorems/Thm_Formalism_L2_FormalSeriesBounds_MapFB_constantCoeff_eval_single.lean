-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_MapFB_constantCoeff_eval_single
-- name    : Formalism.L2.FormalSeriesBounds.MapFB.constantCoeff_eval_single
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:49:09.804961+00:00
-- url     : https://prove2.me/theorems/d60225a1-96ef-4cf4-8131-c646d6fd5669
-- title:
--   Map FB: constant Coeff eval single
-- statement:
--   The Map FB construction uses the constant Coeff eval single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePNabMapSt.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePNabMapSt.lean#L14-L16

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

theorem Formalism.L2.FormalSeriesBounds.MapFB.constantCoeff_eval_single {n : ℕ} (a : Pt K n d) (ha : ∀ i, constantCoeff (a i) = 0) (f : PS K 1 d) :
    constantCoeff (ev ![a] f) = constantCoeff f := by sorry

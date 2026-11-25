-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_MapFB_cc_ev_eq
-- name    : Formalism.L2.FormalSeriesBounds.MapFB.cc_ev_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:33:23.29902+00:00
-- url     : https://prove2.me/theorems/1d30d610-4510-440e-b08c-bf4601a233d8
-- title:
--   Map FB: cc ev eq
-- statement:
--   The Map FB construction uses the cc ev eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePGaugeMapSt.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePGaugeMapSt.lean#L28-L31

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

theorem Formalism.L2.FormalSeriesBounds.MapFB.cc_ev_eq {m n : ℕ} (a : Fin m → Pt R n d) (ha : ∀ j i, constantCoeff (a j i) = 0)
    (f : PS R m d) : constantCoeff (ev a f) = constantCoeff f := by sorry

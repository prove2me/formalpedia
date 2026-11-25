-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_a3uvec_int
-- name    : Formalism.L2.FormalSeriesBounds.a3uvec_int
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:39:57.807388+00:00
-- url     : https://prove2.me/theorems/8eaf4b23-a6cf-4000-b9fe-9b905e882fa0
-- title:
--   Formal Series Bounds: a3uvec int
-- statement:
--   The Formal Series Bounds construction uses the a3uvec int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieLab.lean#L111-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieLab.lean#L111-L115

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_HostTraceIdentity
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePEmbIntSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieLab
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
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {C : Type} [Field C] [CharZero C] {V : VF C}
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

theorem Formalism.L2.FormalSeriesBounds.a3uvec_int (C3 : IntChart T io y) {ι : T.Fr →+* C} (hι : EmbOK T V ι) (ℓ : Lt1 Dw) (i : Fin (chD C3.ch)) :
    V.Ge 0 (ι (chartUnitVectors C3 ℓ i)) := by sorry

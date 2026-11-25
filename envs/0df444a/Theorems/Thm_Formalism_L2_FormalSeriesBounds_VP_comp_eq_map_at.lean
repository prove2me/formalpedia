-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_comp_eq_map_at
-- name    : Formalism.L2.FormalSeriesBounds.VP.comp_eq_map_at
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:41:02.807964+00:00
-- url     : https://prove2.me/theorems/93518e27-86ce-526e-9073-61424a051355
-- title:
--   VP: comp eq map at
-- statement:
--   The VP construction uses the comp eq map at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieValCr.lean#L19-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieValCr.lean#L19-L26

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValBr
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValCr
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

theorem Formalism.L2.FormalSeriesBounds.VP.comp_eq_map_at {n : ℕ} (ε : Pt C 1 dd) (a : Pt C n dd) : comp1 ε a = mapAt ε a := by sorry

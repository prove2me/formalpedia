-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_intS_ps
-- name    : Formalism.L2.FormalSeriesBounds.intS_ps
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:45:56.803813+00:00
-- url     : https://prove2.me/theorems/57137905-668b-434f-904d-263ee92f1f02
-- title:
--   Formal Series Bounds: int S ps
-- statement:
--   The Formal Series Bounds construction uses the int S ps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieCartAdd.lean#L58-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieCartAdd.lean#L58-L67

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartAdd
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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
variable {V : VF C} {τ : Type}

theorem Formalism.L2.FormalSeriesBounds.intS_ps {f : PowerSeries C} : IntS V f ↔ ∀ n, V.Ge 0 (PowerSeries.coeff n f) := by sorry

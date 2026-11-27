-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_eval_points_two
-- name    : Formalism.L2.FormalSeriesBounds.eval_points_two
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-27T05:06:18.928376+00:00
-- url     : https://prove2.me/theorems/565b0166-714e-57a0-9432-dd02f5fe40ac
-- title:
--   Formal Series Bounds: eval points two
-- statement:
--   The Formal Series Bounds construction uses the eval points two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RankMaximalOfNondegenerate.lean#L146-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RankMaximalOfNondegenerate.lean#L146-L153

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RankMaximalOfNondegenerate
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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]

theorem Formalism.L2.FormalSeriesBounds.eval_points_two {dd : ℕ} (f : PS C 2 dd) : ev (n := 2) ![pt C dd 0, pt C dd 1] f = f := by sorry

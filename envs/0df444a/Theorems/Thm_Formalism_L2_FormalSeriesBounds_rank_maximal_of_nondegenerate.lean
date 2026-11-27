-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_rank_maximal_of_nondegenerate
-- name    : Formalism.L2.FormalSeriesBounds.rank_maximal_of_nondegenerate
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-27T05:07:34.302385+00:00
-- url     : https://prove2.me/theorems/e5396c72-5f1f-5c5e-8a5d-badf5c80467a
-- title:
--   Formal Series Bounds: rank maximal of nondegenerate
-- statement:
--   The Formal Series Bounds construction uses the rank maximal of nondegenerate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RankMaximalOfNondegenerate.lean#L325-L352
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RankMaximalOfNondegenerate.lean#L325-L352

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RankMaximalOfNondegenerate
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1

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

theorem Formalism.L2.FormalSeriesBounds.rank_maximal_of_nondegenerate (h1 : RankMaximalInitialCoefficient) : RankMaximalOfNondegenerate := by sorry

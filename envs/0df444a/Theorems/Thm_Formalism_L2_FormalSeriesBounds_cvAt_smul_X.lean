-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_cvAt_smul_X
-- name    : Formalism.L2.FormalSeriesBounds.cvAt_smul_X
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-27T05:13:35.107738+00:00
-- url     : https://prove2.me/theorems/b35e4c8d-815a-573b-9580-9295e3bae0df
-- title:
--   Formal Series Bounds: cv At smul X
-- statement:
--   The Formal Series Bounds construction uses the cv At smul X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RankMaximalOfNondegenerate.lean#L140-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RankMaximalOfNondegenerate.lean#L140-L144

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RankMaximalOfNondegenerate
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

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

theorem Formalism.L2.FormalSeriesBounds.cvAt_smul_X {s : MvPowerSeries (Fin 2) C} (hs : MvPowerSeries.constantCoeff s = 0) (c : C) :
    cvAt s (c • (MvPowerSeries.X () : PowerSeries C)) = c • s := by sorry

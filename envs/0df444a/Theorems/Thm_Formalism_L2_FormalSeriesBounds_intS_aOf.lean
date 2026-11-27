-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_intS_aOf
-- name    : Formalism.L2.FormalSeriesBounds.intS_aOf
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-27T05:34:53.201219+00:00
-- url     : https://prove2.me/theorems/3c3fed4e-6050-5dd8-a278-0bebcf152765
-- title:
--   Formal Series Bounds: int S a Of
-- statement:
--   The Formal Series Bounds construction uses the int S a Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RankMaximalOfNondegenerateOfUnitSeriesIntegral.lean#L78-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RankMaximalOfNondegenerateOfUnitSeriesIntegral.lean#L78-L83

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_FirstStepSecondHalfCondition
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieProj
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RankMaximalOfNondegenerateOfUnitSeriesIntegral
import Theorems.Thm_ReciprocityTheory_PGsh_Up_u1

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

theorem Formalism.L2.FormalSeriesBounds.intS_aOf {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
    (Y : FBChart C V O dd) (h : IntS V Y.u1) (u : Fin dd → C) (hu : ∀ i, V.Ge 0 (u i)) : IntS V (Y.aOf u) := by sorry

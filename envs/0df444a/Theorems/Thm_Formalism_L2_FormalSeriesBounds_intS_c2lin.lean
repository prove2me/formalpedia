-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_intS_c2lin
-- name    : Formalism.L2.FormalSeriesBounds.intS_c2lin
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-27T05:21:37.712252+00:00
-- url     : https://prove2.me/theorems/d4908d8f-bf57-45b0-8fc2-34275fd41027
-- title:
--   Formal Series Bounds: int S c2lin
-- statement:
--   The Formal Series Bounds construction uses the int S c2lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/FirstStepSecondHalfCondition.lean#L47-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/FirstStepSecondHalfCondition.lean#L47-L52

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RankMaximalOfNondegenerate
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_FirstStepSecondHalfCondition
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

theorem Formalism.L2.FormalSeriesBounds.intS_c2lin {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
    (Y : FBChart C V O dd) (u : Fin dd → C) (hu : ∀ i, V.Ge 0 (u i)) : IntS V (Y.chartLinearTerm u) := by sorry

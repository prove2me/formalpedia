-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_SelfConjPoints_inV_cc
-- name    : Formalism.L2.FormalSeriesBounds.SelfConjPoints.inV_cc
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:49:16.137798+00:00
-- url     : https://prove2.me/theorems/b09fb434-f863-4a05-b9c8-f2d3e44d1c27
-- title:
--   Self Conj Points: in V cc
-- statement:
--   The Self Conj Points construction uses the in V cc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/RescaleInV.lean#L39-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/RescaleInV.lean#L39-L41

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieDefs
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RescaleInV
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
open Formalism.L2.FormalSeriesBounds.SelfConjPoints
variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]

theorem Formalism.L2.FormalSeriesBounds.SelfConjPoints.inV_cc (j : Fin 2) {f : PowerSeries C} (hf : PowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (inV j f) = 0 := by sorry

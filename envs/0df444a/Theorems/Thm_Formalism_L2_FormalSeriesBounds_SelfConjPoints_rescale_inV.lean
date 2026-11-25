-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_SelfConjPoints_rescale_inV
-- name    : Formalism.L2.FormalSeriesBounds.SelfConjPoints.rescale_inV
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:49:00.998393+00:00
-- url     : https://prove2.me/theorems/4496258f-1173-4677-9a10-4f0417bae310
-- title:
--   Self Conj Points: rescale in V
-- statement:
--   The Self Conj Points construction uses the rescale in V property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/RescaleInV.lean#L43-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/RescaleInV.lean#L43-L62

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieDefs
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RescaleInV
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_InL_rescale

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

theorem Formalism.L2.FormalSeriesBounds.SelfConjPoints.rescale_inV (w : Fin 2 → C) (j : Fin 2) (f : PowerSeries C) :
    MvPowerSeries.rescale w (inV j f) = inV j (PowerSeries.rescale (w j) f) := by sorry

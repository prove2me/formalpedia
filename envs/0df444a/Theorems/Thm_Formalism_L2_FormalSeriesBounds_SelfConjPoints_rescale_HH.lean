-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_SelfConjPoints_rescale_HH
-- name    : Formalism.L2.FormalSeriesBounds.SelfConjPoints.rescale_HH
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:49:25.204821+00:00
-- url     : https://prove2.me/theorems/431b7dda-7251-41e4-90e4-e718f8df14e1
-- title:
--   Self Conj Points: rescale HH
-- statement:
--   The Self Conj Points construction uses the rescale HH property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/RescaleInV.lean#L64-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/RescaleInV.lean#L64-L83

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieDefs
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RescaleInV
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
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

theorem Formalism.L2.FormalSeriesBounds.SelfConjPoints.rescale_HH (X : RawChart C d I κ) (x z : κ → PowerSeries C) (hx : ∀ i, PowerSeries.constantCoeff (x i) = 0)
    (hz : ∀ i, PowerSeries.constantCoeff (z i) = 0) (w : Fin 2 → C) :
    MvPowerSeries.rescale w (HH X x z) = HH X (rc (w 0) x) (rc (w 1) z) := by sorry

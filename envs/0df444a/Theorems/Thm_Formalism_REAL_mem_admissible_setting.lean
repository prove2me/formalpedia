-- Prove2me | Theorems.Thm_Formalism_REAL_mem_admissible_setting
-- name    : Formalism.REAL.mem_admissible_setting
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:52:06.576567+00:00
-- url     : https://prove2.me/theorems/afba1b00-aa5b-495f-a05d-3461312fbeb3
-- title:
--   REAL: mem admissible setting
-- statement:
--   The REAL construction uses the mem admissible setting property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/IsRightTranslationIsometric.lean#L63-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/IsRightTranslationIsometric.lean#L63-L68

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnGVIff
import Definitions.Def_Formalism_RealPlaceAnalysis_IsRightTranslationIsometric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace ENNReal
noncomputable section
open Formalism Formalism.REAL
attribute [instance] HidaSetting.ng HidaSetting.ips HidaSetting.cs

theorem Formalism.REAL.mem_admissible_setting {n : ℕ} (ε : Fin n → Bool) (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (F : UJ ε → E) : F ∈ (settingG ε E).adm := by sorry

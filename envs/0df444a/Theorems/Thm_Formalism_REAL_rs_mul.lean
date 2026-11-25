-- Prove2me | Theorems.Thm_Formalism_REAL_rs_mul
-- name    : Formalism.REAL.rs_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:52:10.037103+00:00
-- url     : https://prove2.me/theorems/1544e988-81fd-45c0-8a08-d59c05a03206
-- title:
--   REAL: rs mul
-- statement:
--   The REAL construction uses the rs mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/IsRightTranslationIsometric.lean#L76-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/IsRightTranslationIsometric.lean#L76-L79

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

theorem Formalism.REAL.rs_mul {n : ℕ} {ε : Fin n → Bool} {E : Type*} (h₁ h₂ : UJ ε) (F : UJ ε → E) :
    Rs (h₁ * h₂) F = Rs h₁ (Rs h₂ F) := by sorry

-- Prove2me | Theorems.Thm_Formalism_REAL_rs_mem_adm
-- name    : Formalism.REAL.rs_mem_adm
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:52:14.314311+00:00
-- url     : https://prove2.me/theorems/1d4114b3-3e9e-4608-a867-4781f7dede8a
-- title:
--   REAL: rs mem adm
-- statement:
--   The REAL construction uses the rs mem adm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/IsRightTranslationIsometric.lean#L70-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/IsRightTranslationIsometric.lean#L70-L74

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

theorem Formalism.REAL.rs_mem_adm {n : ℕ} {ε : Fin n → Bool} (P : HidaSetting n ε) (F : UJ ε → P.E) (hF : F ∈ P.adm)
    (h : UJ ε) : Rs h F ∈ P.adm := by sorry

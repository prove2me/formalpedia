-- Prove2me | Theorems.Thm_Formalism_HC_Frame_zsmul_generator_eq_zero_of_image
-- name    : Formalism.HC.Frame.zsmul_generator_eq_zero_of_image
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:36:56.224907+00:00
-- url     : https://prove2.me/theorems/73e8cf1b-2c18-5b46-a86d-59bb00ded4eb
-- title:
--   Frame: zsmul generator eq zero of image
-- statement:
--   The Frame construction uses the zsmul generator eq zero of image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ZsmulGeneratorEqZeroOfProjection.lean#L65-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ZsmulGeneratorEqZeroOfProjection.lean#L65-L66

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC
open Formalism.FrobeniusOrbits
open Formalism.HC.Frame
variable (φ : Frame)

theorem Formalism.HC.Frame.zsmul_generator_eq_zero_of_image (k : ℤ) (hk : φ.h (k • φ.a0) = 0) : k • φ.a0 = 0 := by sorry

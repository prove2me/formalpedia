-- Prove2me | Theorems.Thm_Formalism_HC_Frame_dig_def
-- name    : Formalism.HC.Frame.dig_def
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:36:58.780526+00:00
-- url     : https://prove2.me/theorems/f2f7be88-ed9b-4497-92a5-535e955c3218
-- title:
--   Frame: dig def
-- statement:
--   The Frame construction uses the dig def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ZsmulGeneratorEqZeroOfProjection.lean#L74-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ZsmulGeneratorEqZeroOfProjection.lean#L74-L74

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

theorem Formalism.HC.Frame.dig_def (s : ℕ) : φ.dig s = s • φ.a0 := by sorry

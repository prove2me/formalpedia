-- Prove2me | Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- name    : Formalism.HC.Frame.iota_iotaInv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:02:30.023083+00:00
-- url     : https://prove2.me/theorems/a9632efe-ff2e-4bf0-bcf5-0b03289a6e4c
-- title:
--   Frame: iota iota Inv
-- statement:
--   The Frame construction uses the iota iota Inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ZsmulGeneratorEqZeroOfProjection.lean#L132-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ZsmulGeneratorEqZeroOfProjection.lean#L132-L132

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

theorem Formalism.HC.Frame.iota_iotaInv (a : φ.MA) : φ.iota (φ.iotaInv a) = a := by sorry

attribute [defeq] Formalism.HC.Frame.iota_iotaInv

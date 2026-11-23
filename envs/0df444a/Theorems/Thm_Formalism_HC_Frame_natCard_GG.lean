-- Prove2me | Theorems.Thm_Formalism_HC_Frame_natCard_GG
-- name    : Formalism.HC.Frame.natCard_GG
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:39:56.418615+00:00
-- url     : https://prove2.me/theorems/fe9697a8-56ac-4385-b578-f462e570f8e6
-- title:
--   Frame: nat Card GG
-- statement:
--   The Frame construction uses the nat Card GG property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ZsmulGeneratorEqZeroOfProjection.lean#L137-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ZsmulGeneratorEqZeroOfProjection.lean#L137-L144

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

theorem Formalism.HC.Frame.natCard_GG : Nat.card φ.GG = 4 * φ.ord := by sorry

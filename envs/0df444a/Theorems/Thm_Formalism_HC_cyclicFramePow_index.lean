-- Prove2me | Theorems.Thm_Formalism_HC_cyclicFramePow_index
-- name    : Formalism.HC.cyclicFramePow_index
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:37:46.169089+00:00
-- url     : https://prove2.me/theorems/6f70cfbf-7d2c-4efb-b956-7178d774085d
-- title:
--   HC: cyclic Frame Pow index
-- statement:
--   The HC construction uses the cyclic Frame Pow index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/FrameCyclicGenerator.lean#L174-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/FrameCyclicGenerator.lean#L174-L178

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameCyclicGenerator
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
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

theorem Formalism.HC.cyclicFramePow_index (e j : ℕ) (hj : j ≤ e) : (cyclicFramePow e j).o = 2 ^ j := by sorry

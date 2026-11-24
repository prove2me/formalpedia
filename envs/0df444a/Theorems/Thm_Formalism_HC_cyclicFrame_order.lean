-- Prove2me | Theorems.Thm_Formalism_HC_cyclicFrame_order
-- name    : Formalism.HC.cyclicFrame_order
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T16:55:06.6008+00:00
-- url     : https://prove2.me/theorems/705e537d-eef1-4f61-b67a-92369e0da947
-- title:
--   HC: cyclic Frame order
-- statement:
--   The HC construction uses the cyclic Frame order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/FrameCyclicGenerator.lean#L154-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/FrameCyclicGenerator.lean#L154-L156

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

theorem Formalism.HC.cyclicFrame_order (e : ℕ) : (cyclicFrame e).n0 = 2 ^ e := by sorry

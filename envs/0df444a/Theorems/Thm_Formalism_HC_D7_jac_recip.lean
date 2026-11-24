-- Prove2me | Theorems.Thm_Formalism_HC_D7_jac_recip
-- name    : Formalism.HC.D7.jac_recip
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T19:40:59.257326+00:00
-- url     : https://prove2.me/theorems/c672001d-8b5e-4432-8e5a-727a4f5d7832
-- title:
--   D7: jac recip
-- statement:
--   The D7 construction uses the jac recip property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ArtinMapSecondEqJacobiSymOfModEq.lean#L15-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ArtinMapSecondEqJacobiSymOfModEq.lean#L15-L22

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSym
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSymOfModEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC Formalism.HC.D7
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

theorem Formalism.HC.D7.jac_recip {r p : ℕ} (hr : r % 4 = 3) (hp : p % 2 = 1) : jacobiSym (-(r : ℤ)) p = jacobiSym (p : ℤ) r := by sorry

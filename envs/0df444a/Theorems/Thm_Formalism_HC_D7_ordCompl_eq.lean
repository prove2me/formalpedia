-- Prove2me | Theorems.Thm_Formalism_HC_D7_ordCompl_eq
-- name    : Formalism.HC.D7.ordCompl_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:39:24.533778+00:00
-- url     : https://prove2.me/theorems/588d6e58-62fd-40d8-9627-4acd9a205a5d
-- title:
--   D7: ord Compl eq
-- statement:
--   The D7 construction uses the ord Compl eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ArtinMapSecondEqJacobiSymOfModEq.lean#L39-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ArtinMapSecondEqJacobiSymOfModEq.lean#L39-L44

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

theorem Formalism.HC.D7.ordCompl_eq {l m : ℕ} (hl : l.Prime) (k : ℕ) (hm : ¬ l ∣ m) : ordCompl[l] (l ^ k * m) = m := by sorry

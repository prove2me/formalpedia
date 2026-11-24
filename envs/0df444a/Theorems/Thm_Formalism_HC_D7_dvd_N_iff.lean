-- Prove2me | Theorems.Thm_Formalism_HC_D7_dvd_N_iff
-- name    : Formalism.HC.D7.dvd_N_iff
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T19:40:46.273717+00:00
-- url     : https://prove2.me/theorems/bdc97954-7e3b-436d-b333-21d07ac2f2e7
-- title:
--   D7: dvd N iff
-- statement:
--   The D7 construction uses the dvd N iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ArtinMapSecondEqJacobiSymOfModEq.lean#L134-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ArtinMapSecondEqJacobiSymOfModEq.lean#L134-L145

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
variable {q d : ℕ} (e : ℕ) (hH : HostHyp q d)
include hH

theorem Formalism.HC.D7.dvd_N_iff {l : ℕ} (hl : l.Prime) : l ∣ 2 ^ (e + 2) * q * d ↔ l = 2 ∨ l = q ∨ l = d := by sorry

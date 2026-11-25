-- Prove2me | Theorems.Thm_Formalism_HC_HostRaw_Exact_not_sq_dvd
-- name    : Formalism.HC.HostRaw.Exact.not_sq_dvd
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:37:30.244665+00:00
-- url     : https://prove2.me/theorems/bb5c0116-10cd-5400-963c-faf3fe64187d
-- title:
--   Exact: not sq dvd
-- statement:
--   The Exact construction uses the not sq dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/HostRam.lean#L96-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/HostRam.lean#L96-L128

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostRam
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC
open Formalism.FrobeniusOrbits
open Formalism.HC.HostRaw
variable {φ : Frame} (H : HostRaw φ)
variable {H}

theorem Formalism.HC.HostRaw.Exact.not_sq_dvd (hE : H.Exact) (h2 : φ.TwoGroup) {l : ℕ} (hl : l.Prime) (hl2 : l ≠ 2) : ¬ l ^ 2 ∣ H.QS := by sorry

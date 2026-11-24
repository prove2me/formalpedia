-- Prove2me | Theorems.Thm_Formalism_BasicNotions_not_dvd_of_splitK
-- name    : Formalism.BasicNotions.not_dvd_of_splitK
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:31:17.017895+00:00
-- url     : https://prove2.me/theorems/cc7eae2c-20be-4f69-9972-bdf8deb9fd8e
-- title:
--   Basic Notions: not dvd of split K
-- statement:
--   The Basic Notions construction uses the not dvd of split K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/HostCls.lean#L90-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/HostCls.lean#L90-L90

import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_LocalRingCardinality_HostCls
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.FrobeniusOrbits Formalism.HC
open Formalism Formalism.BasicNotions
variable {φ : Frame} (H : HostRaw φ) {p : ℕ}
variable {H}

theorem Formalism.BasicNotions.not_dvd_of_splitK (hp : p.Prime) (h : primeClass H p = .splitK) : ¬ p ∣ H.condN := by sorry

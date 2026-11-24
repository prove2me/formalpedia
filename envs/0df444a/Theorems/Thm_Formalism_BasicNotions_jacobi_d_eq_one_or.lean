-- Prove2me | Theorems.Thm_Formalism_BasicNotions_jacobi_d_eq_one_or
-- name    : Formalism.BasicNotions.jacobi_d_eq_one_or
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:31:09.160003+00:00
-- url     : https://prove2.me/theorems/5498b8d5-0fb3-4bed-b718-2fe0c79df04b
-- title:
--   Basic Notions: jacobi d eq one or
-- statement:
--   The Basic Notions construction uses the jacobi d eq one or property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/HostCls.lean#L96-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/HostCls.lean#L96-L103

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

theorem Formalism.BasicNotions.jacobi_d_eq_one_or (hp : p.Prime) (hd : p ≠ H.d) :
    jacobiSym (-(H.d : ℤ)) p = 1 ∨ jacobiSym (-(H.d : ℤ)) p = -1 := by sorry

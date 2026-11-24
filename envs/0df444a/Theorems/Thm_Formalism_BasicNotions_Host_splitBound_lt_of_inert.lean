-- Prove2me | Theorems.Thm_Formalism_BasicNotions_Host_splitBound_lt_of_inert
-- name    : Formalism.BasicNotions.Host.splitBound_lt_of_inert
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:46:03.238068+00:00
-- url     : https://prove2.me/theorems/f401edd7-7323-4d59-b280-cd667a94f777
-- title:
--   Host: split Bound lt of inert
-- statement:
--   The Host construction uses the split Bound lt of inert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/NotInert.lean#L27-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/NotInert.lean#L27-L28

import Definitions.Def_Formalism_LocalRingCardinality_HostCls
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_NotInert
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HC
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Host
variable {R : Ranks} (H : Host R) {p : ℕ}

theorem Formalism.BasicNotions.Host.splitBound_lt_of_inert (hp : p.Prime) (h : H.cls p = .signal ∨ H.cls p = .inertClass) : H.splitBound < p := by sorry

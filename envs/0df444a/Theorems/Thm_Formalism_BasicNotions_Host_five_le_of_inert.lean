-- Prove2me | Theorems.Thm_Formalism_BasicNotions_Host_five_le_of_inert
-- name    : Formalism.BasicNotions.Host.five_le_of_inert
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:20:55.595651+00:00
-- url     : https://prove2.me/theorems/56a91b84-846b-4734-aeaa-d0b17a9783b1
-- title:
--   Host: five le of inert
-- statement:
--   The Host construction uses the five le of inert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/NotInert.lean#L30-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/NotInert.lean#L30-L33

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

theorem Formalism.BasicNotions.Host.five_le_of_inert (hp : p.Prime) (h3 : 3 ≤ H.splitBound) (h : H.cls p = .signal ∨ H.cls p = .inertClass) : 5 ≤ p := by sorry

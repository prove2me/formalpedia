-- Prove2me | Theorems.Thm_Formalism_BasicNotions_Host_not_inert_of_le_splitBound
-- name    : Formalism.BasicNotions.Host.not_inert_of_le_splitBound
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:46:29.603524+00:00
-- url     : https://prove2.me/theorems/c21f5dc9-67c3-4277-b8be-6ef8e07c7933
-- title:
--   Host: not inert of le split Bound
-- statement:
--   The Host construction uses the not inert of le split Bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/NotInert.lean#L15-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/NotInert.lean#L15-L25

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

theorem Formalism.BasicNotions.Host.not_inert_of_le_splitBound (hp : p.Prime) (h : p ≤ H.splitBound) :
    ¬ (H.cls p = .signal ∨ H.cls p = .inertClass) := by sorry

-- Prove2me | Theorems.Thm_Formalism_BasicNotions_Host_cls_splitK_or_small
-- name    : Formalism.BasicNotions.Host.cls_splitK_or_small
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:20:17.970639+00:00
-- url     : https://prove2.me/theorems/38dc3649-9563-5175-b844-315ebdebe7c0
-- title:
--   Host: cls split K or small
-- statement:
--   The Host construction uses the cls split K or small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/NotInert.lean#L35-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/NotInert.lean#L35-L40

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

theorem Formalism.BasicNotions.Host.cls_splitK_or_small (hp : p.Prime) (h : p ≤ H.splitBound) (hq : p ≠ H.q) (hd : p ≠ H.d) :
    H.cls p = .splitK ∨ p ∈ H.small := by sorry

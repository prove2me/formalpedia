-- Prove2me | Theorems.Thm_Formalism_BasicNotions_Host_primeClass_ne_of_jacobi_one
-- name    : Formalism.BasicNotions.Host.primeClass_ne_of_jacobi_one
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:46:26.85059+00:00
-- url     : https://prove2.me/theorems/d1ec753e-208f-469b-b172-7f06c3b01f79
-- title:
--   Host: prime Class ne of jacobi one
-- statement:
--   The Host construction uses the prime Class ne of jacobi one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/NotInert.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/NotInert.lean#L12-L13

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

theorem Formalism.BasicNotions.Host.primeClass_ne_of_jacobi_one (h : jacobiSym (-(H.d : ℤ)) p = 1) : H.cls p ≠ .inertClass := by sorry

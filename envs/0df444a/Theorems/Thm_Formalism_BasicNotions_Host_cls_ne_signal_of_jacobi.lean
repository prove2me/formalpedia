-- Prove2me | Theorems.Thm_Formalism_BasicNotions_Host_cls_ne_signal_of_jacobi
-- name    : Formalism.BasicNotions.Host.cls_ne_signal_of_jacobi
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:46:03.91159+00:00
-- url     : https://prove2.me/theorems/4dc4c725-d48a-4567-9acd-f568c32a9365
-- title:
--   Host: cls ne signal of jacobi
-- statement:
--   The Host construction uses the cls ne signal of jacobi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/NotInert.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/NotInert.lean#L9-L10

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

theorem Formalism.BasicNotions.Host.cls_ne_signal_of_jacobi (h : jacobiSym (-(H.d : ℤ)) p = 1) : H.cls p ≠ .signal := by sorry

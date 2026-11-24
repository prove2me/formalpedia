-- Prove2me | Theorems.Thm_Formalism_HC_Der_Rd_order_dvd_iff
-- name    : Formalism.HC.Der.Rd.order_dvd_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:52.264604+00:00
-- url     : https://prove2.me/theorems/efae0642-16f8-4041-b363-2bc234a85620
-- title:
--   Rd: order dvd iff
-- statement:
--   The Rd construction uses the order dvd iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RdArith.lean#L141-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RdArith.lean#L141-L153

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdArith
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ArithmeticFunction Finset
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der Formalism.HC.Der.Rd
variable {N : ℕ} [NeZero N]

theorem Formalism.HC.Der.Rd.order_dvd_iff {m : ℕ} (hm : m ∣ N) (u : ZMod N) : addOrderOf (u - 1) ∣ m ↔ u.val ≡ 1 [MOD N / m] := by sorry

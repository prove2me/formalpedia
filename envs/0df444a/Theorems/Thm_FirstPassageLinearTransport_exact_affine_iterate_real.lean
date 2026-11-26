-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_exact_affine_iterate_real
-- name    : FirstPassageLinearTransport.exact_affine_iterate_real
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:02:16.027964+00:00
-- url     : https://prove2.me/theorems/be5690b3-0f48-59a3-b88c-3448588f8ed8
-- title:
--   First Passage Linear Transport: exact affine iterate real
-- statement:
--   Real-valued exact affine iteration, used by the analytic barrier and
--   bootstrap layers.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Parity.lean#L273-L306
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Parity.lean#L273-L306

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.NormNum.Parity
import Definitions.Def_FirstPassageLinearTransport_Basic
import Definitions.Def_FirstPassageLinearTransport_Parity
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators

theorem FirstPassageLinearTransport.exact_affine_iterate_real (n k : ℕ) :
    (orbit k n : ℝ) =
      (3 : ℝ) ^ (oddCount n k) / (2 : ℝ) ^ k * (n : ℝ) +
        ∑ i ∈ Finset.range k,
          ((parityBit n i : ℕ) : ℝ) *
            (3 : ℝ) ^ (oddCount n k - oddCount n (i + 1)) /
              (2 : ℝ) ^ (k - i) := by sorry

-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_exact_affine_iterate
-- name    : FirstPassageLinearTransport.exact_affine_iterate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:21:39.652592+00:00
-- url     : https://prove2.me/theorems/af79a216-46df-4b84-86ba-2487e8254520
-- title:
--   First Passage Linear Transport: exact affine iterate
-- statement:
--   Exact affine iteration in the literal rational form used by the manuscript.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Parity.lean#L256-L269
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Parity.lean#L256-L269

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.NormNum.Parity
import Definitions.Def_FirstPassageLinearTransport_Basic
import Definitions.Def_FirstPassageLinearTransport_Parity
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators

theorem FirstPassageLinearTransport.exact_affine_iterate (n k : ℕ) :
    (orbit k n : ℚ) =
      (3 : ℚ) ^ (oddCount n k) / (2 : ℚ) ^ k * (n : ℚ) +
        affineCorrectionQ n k := by sorry

-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_exact_affine_iterate_scaled
-- name    : FirstPassageLinearTransport.exact_affine_iterate_scaled
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T10:59:20.344134+00:00
-- url     : https://prove2.me/theorems/67af9acb-b9eb-5ed8-ae3b-1e272d0a31b4
-- title:
--   First Passage Linear Transport: exact affine iterate scaled
-- statement:
--   Exact affine iteration in division-free form.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Parity.lean#L204-L232
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Parity.lean#L204-L232

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.NormNum.Parity
import Definitions.Def_FirstPassageLinearTransport_Basic
import Definitions.Def_FirstPassageLinearTransport_Parity
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators

theorem FirstPassageLinearTransport.exact_affine_iterate_scaled (n k : ℕ) :
    2 ^ k * orbit k n =
      3 ^ (oddCount n k) * n + affineCorrection n k := by sorry

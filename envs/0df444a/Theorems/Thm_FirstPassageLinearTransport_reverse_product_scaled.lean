-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_reverse_product_scaled
-- name    : FirstPassageLinearTransport.reverse_product_scaled
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:07:29.208021+00:00
-- url     : https://prove2.me/theorems/31e21d2d-0900-5ff8-8a77-b33e17e80231
-- title:
--   First Passage Linear Transport: reverse product scaled
-- statement:
--   Exact reverse-product identity with the power of three cleared.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstPassage.lean#L91-L121
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstPassage.lean#L91-L121

import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_FirstPassage
set_option autoImplicit true
open FirstPassageLinearTransport

theorem FirstPassageLinearTransport.reverse_product_scaled {n : ℕ} (hn : 0 < n) (h : ℕ) :
    (3 : ℚ) ^ (oddCount n h) * (n : ℚ) =
      (2 : ℚ) ^ h * (orbit h n : ℚ) * reverseProduct n h := by sorry

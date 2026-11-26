-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_reverse_product_identity
-- name    : FirstPassageLinearTransport.reverse_product_identity
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T10:59:43.564686+00:00
-- url     : https://prove2.me/theorems/0853c027-12a7-51dc-bbf4-19113a86ad53
-- title:
--   First Passage Linear Transport: reverse product identity
-- statement:
--   Exact reverse product in the manuscript normalization.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstPassage.lean#L124-L131
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstPassage.lean#L124-L131

import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_FirstPassage
set_option autoImplicit true
open FirstPassageLinearTransport

theorem FirstPassageLinearTransport.reverse_product_identity {n : ℕ} (hn : 0 < n) (h : ℕ) :
    (n : ℚ) =
      ((2 : ℚ) ^ h * (orbit h n : ℚ) /
        (3 : ℚ) ^ (oddCount n h)) * reverseProduct n h := by sorry

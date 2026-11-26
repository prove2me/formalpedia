-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_reverseProduct_eq_prod_loss
-- name    : FirstPassageLinearTransport.reverseProduct_eq_prod_loss
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T10:59:51.982798+00:00
-- url     : https://prove2.me/theorems/ef44cf98-5cca-4b1a-bc4d-af5bb6e5bfb4
-- title:
--   First Passage Linear Transport: reverse Product eq prod loss
-- statement:
--   The First Passage Linear Transport construction uses the reverse Product eq prod loss property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstPassage.lean#L145-L148
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstPassage.lean#L145-L148

import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_FirstPassage
set_option autoImplicit true
open FirstPassageLinearTransport

theorem FirstPassageLinearTransport.reverseProduct_eq_prod_loss (n h : ℕ) :
    reverseProduct n h =
      ∏ i ∈ Finset.range h, (1 - reverseLoss n i) := by sorry

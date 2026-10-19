-- Prove2me | Theorems.Thm_ENNReal_cancel_common_numerator_in_division_ratio
-- name    : ENNReal.cancel_common_numerator_in_division_ratio
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:57:03.329542+00:00
-- url     : https://prove2.me/theorems/989152a6-bf5c-4e32-862d-4128c96e4068
-- title:
--   ENNReal.cancel_common_numerator_in_division_ratio
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | SpherePacking | external Lean 4.33.1 validation; bundle SHA256 ecca43e9570778e44777003bd5984d4ec94cd395fce5324c69b88ac50ad79ed2

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

theorem ENNReal.cancel_common_numerator_in_division_ratio {a b c : ENNReal} (ha : a ≠ 0) (ha' : a ≠ ⊤)
    (hc : c ≠ ⊤) :
    (a / b) / (a / c) = c / b := by sorry

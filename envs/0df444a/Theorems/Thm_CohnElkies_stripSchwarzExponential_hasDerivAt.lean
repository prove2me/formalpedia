-- Prove2me | Theorems.Thm_CohnElkies_stripSchwarzExponential_hasDerivAt
-- name    : CohnElkies.stripSchwarzExponential_hasDerivAt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:52.291105+00:00
-- url     : https://prove2.me/theorems/e0bfe4fb-4406-4ef9-b41a-c7da35b2d110
-- title:
--   CohnElkies.stripSchwarzExponential_hasDerivAt
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | SpherePacking | external Lean 4.33.1 validation; bundle SHA256 ecca43e9570778e44777003bd5984d4ec94cd395fce5324c69b88ac50ad79ed2

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology

theorem CohnElkies.stripSchwarzExponential_hasDerivAt
    (ℓ : ℝ) (z : ℂ) (y : ℝ) :
    HasDerivAt
      (fun w : ℂ => stripSchwarzExponential ℓ w y)
      (stripSchwarzExponential ℓ z y *
        ((Real.pi : ℂ) / (2 * (ℓ : ℂ)))) z := by sorry

-- Prove2me | Theorems.Thm_CohnElkies_plusSaddleSmallRadiusPolynomial_error
-- name    : CohnElkies.plusSaddleSmallRadiusPolynomial_error
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:55.583848+00:00
-- url     : https://prove2.me/theorems/abc53792-41e9-4334-b676-cf76c083e30a
-- title:
--   CohnElkies.plusSaddleSmallRadiusPolynomial_error
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
open scoped Topology

theorem CohnElkies.plusSaddleSmallRadiusPolynomial_error
    {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (n : ℕ) (hn : 2 * (n : ℝ) ≤ ℓ) :
    |((beta ε - (2 * (n : ℝ) / ℓ) *
          (2 + 2 * (n : ℝ) / ℓ) ^ 2) /
        beta ε) - 1| ≤
      (18 / beta ε) * ((n : ℝ) / ℓ) := by sorry

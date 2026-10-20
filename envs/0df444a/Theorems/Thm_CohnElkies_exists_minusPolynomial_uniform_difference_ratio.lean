-- Prove2me | Theorems.Thm_CohnElkies_exists_minusPolynomial_uniform_difference_ratio
-- name    : CohnElkies.exists_minusPolynomial_uniform_difference_ratio
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:54.903436+00:00
-- url     : https://prove2.me/theorems/309cdc8d-d8ab-4eae-b3a2-7ee732d7d1fa
-- title:
--   CohnElkies.exists_minusPolynomial_uniform_difference_ratio
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

theorem CohnElkies.exists_minusPolynomial_uniform_difference_ratio
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ u : ℝ, 1 + ε / 4 ≤ u → ∀ T : ℝ,
        ‖minusPolynomial ε
              ((T : ℂ) + Complex.I * (u : ℂ)) -
            minusPolynomial ε (Complex.I * (u : ℂ))‖ /
          ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ ≤
            C * (|T| + |T| ^ 3) := by sorry

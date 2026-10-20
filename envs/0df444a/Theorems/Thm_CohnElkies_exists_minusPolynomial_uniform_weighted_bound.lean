-- Prove2me | Theorems.Thm_CohnElkies_exists_minusPolynomial_uniform_weighted_bound
-- name    : CohnElkies.exists_minusPolynomial_uniform_weighted_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:59.395342+00:00
-- url     : https://prove2.me/theorems/c480f907-32ae-4047-9f59-ce2dbbda58e4
-- title:
--   CohnElkies.exists_minusPolynomial_uniform_weighted_bound
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
open Filter Set
open scoped Topology

theorem CohnElkies.exists_minusPolynomial_uniform_weighted_bound
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ u : ℝ, 1 + ε / 4 ≤ u → ∀ T : ℝ,
        ‖minusPolynomial ε
          ((T : ℂ) + Complex.I * (u : ℂ))‖ ≤
          C * (1 + |T| ^ 3) *
            ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ := by sorry

-- Prove2me | Theorems.Thm_CohnElkies_plusSaddlePoleResidue_mul_pow_eq_smallCoefficient
-- name    : CohnElkies.plusSaddlePoleResidue_mul_pow_eq_smallCoefficient
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:55.583848+00:00
-- url     : https://prove2.me/theorems/c3bcb22c-d176-486b-8165-7528e7f3ecfd
-- title:
--   CohnElkies.plusSaddlePoleResidue_mul_pow_eq_smallCoefficient
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

theorem CohnElkies.plusSaddlePoleResidue_mul_pow_eq_smallCoefficient
    {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (n : ℕ) (r : ℝ) :
    plusSaddlePoleResidue ε ℓ n *
        ((r ^ (2 * n) : ℝ) : ℂ) =
      ((saddleOriginValue ε ℓ *
        ((-saddleSmallRadiusVariable ε r) ^ n /
          (n.factorial : ℝ)) *
        plusSaddleSmallRadiusCoefficient ε ℓ n : ℝ) : ℂ) := by sorry

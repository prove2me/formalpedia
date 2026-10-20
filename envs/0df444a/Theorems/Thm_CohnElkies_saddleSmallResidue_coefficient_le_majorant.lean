-- Prove2me | Theorems.Thm_CohnElkies_saddleSmallResidue_coefficient_le_majorant
-- name    : CohnElkies.saddleSmallResidue_coefficient_le_majorant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:56.845665+00:00
-- url     : https://prove2.me/theorems/234b989a-c142-406e-b3d6-e260eea9fa45
-- title:
--   CohnElkies.saddleSmallResidue_coefficient_le_majorant
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

theorem CohnElkies.saddleSmallResidue_coefficient_le_majorant
    {K C ℓ y : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hℓ : 1 ≤ ℓ)
    (hy : 0 ≤ y)
    (hyupper : y ≤ Real.log ℓ / 8 + C) :
    (K / ℓ) *
        Real.exp
          (K * (saddleSmallResidueTruncation ℓ : ℝ) ^ 2 / ℓ) *
        (2 * y + y ^ 2) * Real.exp (2 * y) ≤
      saddleSmallResidueCoefficientMajorant K C ℓ := by sorry

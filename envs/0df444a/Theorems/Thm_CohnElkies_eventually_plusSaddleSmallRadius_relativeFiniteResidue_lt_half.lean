-- Prove2me | Theorems.Thm_CohnElkies_eventually_plusSaddleSmallRadius_relativeFiniteResidue_lt_half
-- name    : CohnElkies.eventually_plusSaddleSmallRadius_relativeFiniteResidue_lt_half
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:56.845665+00:00
-- url     : https://prove2.me/theorems/7b05f4e9-8486-4386-815f-196040056874
-- title:
--   CohnElkies.eventually_plusSaddleSmallRadius_relativeFiniteResidue_lt_half
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

theorem CohnElkies.eventually_plusSaddleSmallRadius_relativeFiniteResidue_lt_half
    {ε : ℝ}
    (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ ℓ : ℝ in atTop,
      ∀ y : ℝ,
        0 ≤ y → y ≤ Real.log ℓ / 8 + C →
          Real.exp y *
            |(∑ n ∈ Finset.range
                (saddleSmallResidueTruncation ℓ + 1),
              ((-y) ^ n / (n.factorial : ℝ)) *
                plusSaddleSmallRadiusCoefficient ε ℓ n) -
              Real.exp (-y)| < 1 / 2 := by sorry

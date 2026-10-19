-- Prove2me | Theorems.Thm_CohnElkies_saddleSmallRadiusVariable_star_eq
-- name    : CohnElkies.saddleSmallRadiusVariable_star_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:56.260927+00:00
-- url     : https://prove2.me/theorems/ec14bb82-4c75-4290-ab29-3cdf3604047e
-- title:
--   CohnElkies.saddleSmallRadiusVariable_star_eq
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

theorem CohnElkies.saddleSmallRadiusVariable_star_eq
    {ε : ℝ} {d : ℕ} (hd : 0 < d) :
    saddleSmallRadiusVariable ε (saddleSmallRadiusStar ε d) =
      Real.exp
        (saddleDigamma
            (Real.log ((d : ℝ) / 2) / 8) +
          2 *
            (saddleShellDerivativeOne ε +
              saddleSourceShellDerivative ε
                (saddleSmallRadiusStarOrdinate ε d))) := by sorry

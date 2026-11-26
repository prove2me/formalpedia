-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedSourceWeight_mul_fixedRenyiMoment_le_sharp
-- name    : CollatzEndpointTransport.FixedTotal.fixedSourceWeight_mul_fixedRenyiMoment_le_sharp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:11:02.593283+00:00
-- url     : https://prove2.me/theorems/305f5323-5b7f-572e-a7fb-812dc72bae8d
-- title:
--   Fixed Total: fixed Source Weight mul fixed Renyi Moment le sharp
-- statement:
--   The fixed-total central moment with its exact source-weight factor
--   `p^(1-theta)` retained.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/SharpCentralRenyiPullback.lean#L84-L147
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/SharpCentralRenyiPullback.lean#L84-L147

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.fixedSourceWeight_mul_fixedRenyiMoment_le_sharp
    {N s : ℕ} {theta eta : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2)
    (hN : 1 < N) (hs1 : 1 < s) (hsN : s < N)
    (hcen : InCentralRenyiWindow N s eta)
    (hsizePi :
      2 * eta ≤ centralRenyiGap theta eta * ((N : ℝ) - 1))
    (hsizeDrift :
      (1 / 2 : ℝ) ≤
        (Real.log 2 / Real.log 3 - (1 / 2 + eta)) * N) :
    fixedSourceWeight N s * fixedRenyiMoment N s theta ≤
      centralMomentConstant theta eta * (N + 1) *
        (fixedSourceWeight N s) ^ (1 - theta) := by sorry

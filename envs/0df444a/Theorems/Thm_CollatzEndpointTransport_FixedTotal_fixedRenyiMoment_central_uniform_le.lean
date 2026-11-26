-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedRenyiMoment_central_uniform_le
-- name    : CollatzEndpointTransport.FixedTotal.fixedRenyiMoment_central_uniform_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:37:38.397353+00:00
-- url     : https://prove2.me/theorems/db649e6b-fd04-5287-a13f-0800b4cb9edd
-- title:
--   Fixed Total: fixed Renyi Moment central uniform le
-- statement:
--   Uniform central fixed-level moment with the geometric denominator
--   replaced by the fixed interior ratio.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L1273-L1335
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L1273-L1335

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.fixedRenyiMoment_central_uniform_le
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
    fixedRenyiMoment N s theta ≤
      4 * (((2 : ℝ) ^ N) ^ theta) /
          (((fixedSet N s).card : ℝ) ^ theta) *
        ((N : ℝ) * (3 : ℝ) ^ (-theta) /
          (1 - centralRenyiRatio theta
            (centralRenyiPiStar theta eta)) + 2) := by sorry

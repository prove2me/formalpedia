-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedRenyiMoment_central_uniform_le_fixedSize
-- name    : CollatzEndpointTransport.FixedTotal.fixedRenyiMoment_central_uniform_le_fixedSize
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:40:36.830868+00:00
-- url     : https://prove2.me/theorems/fdf912fc-5261-54f4-87bd-d0a822498adc
-- title:
--   Fixed Total: fixed Renyi Moment central uniform le fixed Size
-- statement:
--   Central fixed-level moment with a uniform constant and no factor of N.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedSizeCentralRenyiMoment.lean#L106-L205
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedSizeCentralRenyiMoment.lean#L106-L205

import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeSeparatorReverse
import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeCentralRenyiMoment
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.fixedRenyiMoment_central_uniform_le_fixedSize
    {N s : ℕ} {theta eta : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2)
    (hN : 2 < N) (hs1 : 1 < s) (hsN : s < N)
    (hcen : InCentralRenyiWindow N s eta)
    (hsizePi :
      2 * eta ≤ centralRenyiGap theta eta * ((N : ℝ) - 1))
    (hsizeDrift :
      (1 / 2 : ℝ) ≤
        (Real.log 2 / Real.log 3 - (1 / 2 + eta)) * N) :
    fixedRenyiMoment N s theta ≤
      fixedSizeCentralMomentConstant theta eta *
        ((((2 : ℝ) ^ N) ^ theta) /
          (((fixedSet N s).card : ℝ) ^ theta)) := by sorry

-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedSourceWeight_mul_fixedRenyiMoment_le_fixedSize
-- name    : CollatzEndpointTransport.FixedTotal.fixedSourceWeight_mul_fixedRenyiMoment_le_fixedSize
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:10:19.18891+00:00
-- url     : https://prove2.me/theorems/7bc2cecd-1c86-5689-8bfd-61803e8a876f
-- title:
--   Fixed Total: fixed Source Weight mul fixed Renyi Moment le fixed Size
-- statement:
--   One central level weighted by its exact source probability.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedSizeCentralRenyiMoment.lean#L208-L242
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedSizeCentralRenyiMoment.lean#L208-L242

import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeSeparatorReverse
import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeCentralRenyiMoment
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.fixedSourceWeight_mul_fixedRenyiMoment_le_fixedSize
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
    fixedSourceWeight N s * fixedRenyiMoment N s theta ≤
      fixedSizeCentralMomentConstant theta eta *
        (fixedSourceWeight N s) ^ (1 - theta) := by sorry

-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedRenyiMoment_central_le
-- name    : CollatzEndpointTransport.FixedTotal.fixedRenyiMoment_central_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:37:23.70861+00:00
-- url     : https://prove2.me/theorems/fba6030c-622d-538d-a924-6313963414ea
-- title:
--   Fixed Total: fixed Renyi Moment central le
-- statement:
--   Central fixed-level moment with explicit geometric denominator.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L1132-L1167
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L1132-L1167

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real NNReal
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.fixedRenyiMoment_central_le
    {N s : ℕ} {theta : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta ≤ 1)
    (hN : 1 < N) (hs1 : 1 < s) (hsN : s < N)
    (hpiAlpha :
      centralSeparatorProportion N s < centralRenyiAlpha theta)
    (hcontract : 3 ^ s ≤ 2 ^ N) :
    fixedRenyiMoment N s theta ≤
      4 * (((2 : ℝ) ^ N) ^ theta) /
          (((fixedSet N s).card : ℝ) ^ theta) *
        ((N : ℝ) * (3 : ℝ) ^ (-theta) /
          (1 - centralRenyiRatio theta
            (centralSeparatorProportion N s)) + 2) := by sorry

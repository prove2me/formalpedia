-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedLiftMoment_div_scale_card_le
-- name    : CollatzEndpointTransport.FixedTotal.fixedLiftMoment_div_scale_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:37:21.571767+00:00
-- url     : https://prove2.me/theorems/9a379e06-fee2-4318-b0c4-14860a76a747
-- title:
--   Fixed Total: fixed Lift Moment div scale card le
-- statement:
--   The normalized source-side lift moment is controlled by the average
--   recursive majorant.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L1057-L1089
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L1057-L1089

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

theorem CollatzEndpointTransport.FixedTotal.fixedLiftMoment_div_scale_card_le
    {N s : ℕ} {theta : ℝ}
    (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (hcard : 0 < (fixedSet N s).card) :
    fixedLiftMoment N s theta /
        ((((2 : ℝ) ^ N) ^ theta) * ((fixedSet N s).card : ℝ)) ≤
      fixedReverseMajorantAverage N s theta := by sorry

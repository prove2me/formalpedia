-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedRenyiMoment_le_reverseAverage
-- name    : CollatzEndpointTransport.FixedTotal.fixedRenyiMoment_le_reverseAverage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:37:21.592419+00:00
-- url     : https://prove2.me/theorems/33fedfe8-ae30-5f8b-bc7d-8cdcd6ae9538
-- title:
--   Fixed Total: fixed Renyi Moment le reverse Average
-- statement:
--   Fixed-level Renyi moment in terms of the exact reverse-spend average.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L1092-L1129
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L1092-L1129

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

theorem CollatzEndpointTransport.FixedTotal.fixedRenyiMoment_le_reverseAverage
    {N s : ℕ} {theta : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta ≤ 1)
    (hcard : 0 < (fixedSet N s).card) :
    fixedRenyiMoment N s theta ≤
      4 * (((2 : ℝ) ^ N) ^ theta) *
        fixedReverseMajorantAverage N s theta /
          (((fixedSet N s).card : ℝ) ^ theta) := by sorry

-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_tsum_shifted_choose_mul_geometric
-- name    : CollatzEndpointTransport.FixedTotal.tsum_shifted_choose_mul_geometric
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:36:55.916147+00:00
-- url     : https://prove2.me/theorems/70957371-bb08-44d5-8d1b-6d2251ff8a9d
-- title:
--   Fixed Total: tsum shifted choose mul geometric
-- statement:
--   Exact negative-binomial generating series.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L592-L599
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L592-L599

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.tsum_shifted_choose_mul_geometric
    {q : ℝ} (r : ℕ) (hr : 0 < r) (hq : ‖q‖ < 1) :
    ∑' n : ℕ, ((n + r - 1).choose (r - 1) : ℝ) * q ^ n =
      1 / (1 - q) ^ r := by sorry

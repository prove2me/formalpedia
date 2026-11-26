-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_tsum_terminal_majorant
-- name    : CollatzEndpointTransport.FixedTotal.tsum_terminal_majorant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:36:57.820984+00:00
-- url     : https://prove2.me/theorems/b602df5b-171f-53a6-9f5f-deccf05176e8
-- title:
--   Fixed Total: tsum terminal majorant
-- statement:
--   Closed form of the negative-binomial terminal majorant.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L663-L686
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L663-L686

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

theorem CollatzEndpointTransport.FixedTotal.tsum_terminal_majorant
    {theta pi : ℝ} {r : ℕ}
    (htheta : 0 < theta) (hpi0 : 0 ≤ pi) (hpi1 : pi ≤ 1)
    (hr : 0 < r) :
    ∑' n : ℕ,
        pi ^ r * (1 - pi) ^ n *
          ((n + r - 1).choose (r - 1) : ℝ) *
          realTerminalSpendTerm theta r (n + r) =
      (3 : ℝ) ^ (-theta) *
        centralRenyiRatio theta pi ^ r := by sorry

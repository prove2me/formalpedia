-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_summable_terminal_majorant
-- name    : CollatzEndpointTransport.FixedTotal.summable_terminal_majorant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:36:54.102542+00:00
-- url     : https://prove2.me/theorems/be494784-f441-4b49-aceb-2ddcbc6685d4
-- title:
--   Fixed Total: summable terminal majorant
-- statement:
--   The Fixed Total construction uses the summable terminal majorant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L643-L660
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L643-L660

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

theorem CollatzEndpointTransport.FixedTotal.summable_terminal_majorant
    {theta pi : ℝ} {r : ℕ}
    (htheta : 0 < theta) (hpi0 : 0 ≤ pi) (hpi1 : pi ≤ 1)
    (hr : 0 < r) :
    Summable fun n : ℕ =>
      pi ^ r * (1 - pi) ^ n *
        ((n + r - 1).choose (r - 1) : ℝ) *
        realTerminalSpendTerm theta r (n + r) := by sorry

-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_shifted_terminal_majorant_eq
-- name    : CollatzEndpointTransport.FixedTotal.shifted_terminal_majorant_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:34:33.77883+00:00
-- url     : https://prove2.me/theorems/b004e2cd-a0ce-4024-90dc-1208dbec0102
-- title:
--   Fixed Total: shifted terminal majorant eq
-- statement:
--   The fixed-spend terminal term with `D = r+n` factors into the
--   negative-binomial tail ratio.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L611-L641
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L611-L641

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

theorem CollatzEndpointTransport.FixedTotal.shifted_terminal_majorant_eq
    {theta pi : ℝ} {r n : ℕ} (hr : 0 < r) :
    pi ^ r * (1 - pi) ^ n *
          ((n + r - 1).choose (r - 1) : ℝ) *
          realTerminalSpendTerm theta r (n + r) =
      (3 : ℝ) ^ (-theta) *
        (((3 : ℝ) ^ theta * pi / (2 : ℝ) ^ theta) ^ r) *
        (((n + r - 1).choose (r - 1) : ℝ) *
          centralReverseTailRatio theta pi ^ n) := by sorry

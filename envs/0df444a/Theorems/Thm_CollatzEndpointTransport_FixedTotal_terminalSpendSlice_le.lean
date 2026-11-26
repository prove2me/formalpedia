-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_terminalSpendSlice_le
-- name    : CollatzEndpointTransport.FixedTotal.terminalSpendSlice_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:36:51.340078+00:00
-- url     : https://prove2.me/theorems/35839ed3-5147-4dcc-a539-db8ac9485972
-- title:
--   Fixed Total: terminal Spend Slice le
-- statement:
--   One fixed-spend slice is bounded by the product of its possible
--   terminal patterns and compatible prefixes.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L374-L438
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L374-L438

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

theorem CollatzEndpointTransport.FixedTotal.terminalSpendSlice_le
    {N s r D : ℕ} (theta : ℝ)
    (hr0 : 0 < r) (hrs : r < s) :
    (∑ d ∈ terminalPatternSet N s r D,
        (terminalFiber N s r d).card *
          realTerminalPatternTerm theta r d) ≤
      ((D - 1).choose (r - 1) : ℝ) *
        ((N - D - 1).choose (s - r - 1) : ℝ) *
          realTerminalSpendTerm theta r D := by sorry

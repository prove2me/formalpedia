-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_terminalSpendSlice_div_card_le
-- name    : CollatzEndpointTransport.FixedTotal.terminalSpendSlice_div_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:37:00.042878+00:00
-- url     : https://prove2.me/theorems/798fcbf4-b63d-4aba-8fe7-0b2905d90bd5
-- title:
--   Fixed Total: terminal Spend Slice div card le
-- statement:
--   Conditional probability form of the fixed-spend estimate.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L441-L538
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L441-L538

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

theorem CollatzEndpointTransport.FixedTotal.terminalSpendSlice_div_card_le
    {N s r D : ℕ} (theta : ℝ)
    (hN : 1 < N) (hs1 : 1 < s) (hsN : s < N)
    (hr0 : 0 < r) (hrs : r < s) :
    (∑ d ∈ terminalPatternSet N s r D,
        (terminalFiber N s r d).card *
          realTerminalPatternTerm theta r d) /
          ((fixedSet N s).card : ℝ) ≤
      (N : ℝ) *
        centralSeparatorProportion N s ^ r *
        (1 - centralSeparatorProportion N s) ^ (D - r) *
        ((D - 1).choose (r - 1) : ℝ) *
        realTerminalSpendTerm theta r D := by sorry

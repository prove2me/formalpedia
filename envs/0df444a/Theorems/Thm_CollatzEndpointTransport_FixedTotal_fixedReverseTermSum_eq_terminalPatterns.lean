-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedReverseTermSum_eq_terminalPatterns
-- name    : CollatzEndpointTransport.FixedTotal.fixedReverseTermSum_eq_terminalPatterns
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:36:36.448932+00:00
-- url     : https://prove2.me/theorems/eeb192f0-99a9-4958-bb74-b88647de5c56
-- title:
--   Fixed Total: fixed Reverse Term Sum eq terminal Patterns
-- statement:
--   Exact partition of one reverse-spend sum by the terminal block list.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L344-L354
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L344-L354

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

theorem CollatzEndpointTransport.FixedTotal.fixedReverseTermSum_eq_terminalPatterns
    (N s : ℕ) (theta : ℝ) (r : ℕ) :
    fixedReverseTermSum N s theta r =
      ∑ d ∈ terminalPatternImage N s r,
        (terminalFiber N s r d).card *
          realTerminalPatternTerm theta r d := by sorry

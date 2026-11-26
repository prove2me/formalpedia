-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedReverseTermSum_eq_spend
-- name    : CollatzEndpointTransport.FixedTotal.fixedReverseTermSum_eq_spend
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:36:36.492677+00:00
-- url     : https://prove2.me/theorems/9146070c-faaa-54dc-8580-f56db3a07f7a
-- title:
--   Fixed Total: fixed Reverse Term Sum eq spend
-- statement:
--   Exact further partition by the total terminal spend.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L357-L370
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L357-L370

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

theorem CollatzEndpointTransport.FixedTotal.fixedReverseTermSum_eq_spend
    (N s : ℕ) (theta : ℝ) (r : ℕ) :
    fixedReverseTermSum N s theta r =
      ∑ D ∈ range (N + 1),
        ∑ d ∈ terminalPatternSet N s r D,
          (terminalFiber N s r d).card *
            realTerminalPatternTerm theta r d := by sorry

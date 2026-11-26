-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_realReverseMajorant_le_nonterminal_add_two
-- name    : CollatzEndpointTransport.FixedTotal.realReverseMajorant_le_nonterminal_add_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:37:12.807832+00:00
-- url     : https://prove2.me/theorems/fc231d04-2454-5de5-bed5-124e479b3737
-- title:
--   Fixed Total: real Reverse Majorant le nonterminal add two
-- statement:
--   Once the multiplicative coefficient is contracting, the final exposed
--   reverse prefix and the remaining tail each cost at most one.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L911-L939
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L911-L939

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

theorem CollatzEndpointTransport.FixedTotal.realReverseMajorant_le_nonterminal_add_two
    {N s : ℕ} {theta : ℝ}
    (htheta : 0 ≤ theta) (hs0 : 0 < s)
    (hcontract : 3 ^ s ≤ 2 ^ N)
    (c : Composition N) (hc : c ∈ fixedSet N s) :
    realReverseMajorant theta c ≤
      (∑ r ∈ Ico 1 s, realReverseMomentTerm theta c r) + 2 := by sorry

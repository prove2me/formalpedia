-- Prove2me | Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_card_badPrefix_le_sum
-- name    : CollatzEndpointTransport.QuantitativeDensity.card_badPrefix_le_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:10:01.248801+00:00
-- url     : https://prove2.me/theorems/87222f3e-8d48-5d22-9a34-74617ad5a754
-- title:
--   Quantitative Density: card bad Prefix le sum
-- statement:
--   Cardinality form of the shell decomposition.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/ShellToGlobalDensity.lean#L67-L76
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/ShellToGlobalDensity.lean#L67-L76

import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensity
import Definitions.Def_CollatzEndpointTransport_Common_ShellToGlobalDensity
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.QuantitativeDensity
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.QuantitativeDensity.card_badPrefix_le_sum (S : Set ℕ) (N : ℕ) :
    (badPrefix S N).card ≤
      ∑ M ∈ Finset.range (Nat.log 2 N + 1), (shellBad S M).card := by sorry

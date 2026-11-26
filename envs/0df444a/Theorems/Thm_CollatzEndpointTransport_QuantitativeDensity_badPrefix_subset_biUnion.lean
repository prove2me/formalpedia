-- Prove2me | Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_badPrefix_subset_biUnion
-- name    : CollatzEndpointTransport.QuantitativeDensity.badPrefix_subset_biUnion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:10:16.042104+00:00
-- url     : https://prove2.me/theorems/9d058d0f-fcf2-4dc9-bcc3-173f98b9554e
-- title:
--   Quantitative Density: bad Prefix subset bi Union
-- statement:
--   Every positive `n <= N` lies in a dyadic shell of index at most
--   `Nat.log 2 N`.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/ShellToGlobalDensity.lean#L51-L64
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/ShellToGlobalDensity.lean#L51-L64

import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensity
import Definitions.Def_CollatzEndpointTransport_Common_ShellToGlobalDensity
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.QuantitativeDensity
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.QuantitativeDensity.badPrefix_subset_biUnion (S : Set ℕ) (N : ℕ) :
    badPrefix S N ⊆
      (Finset.range (Nat.log 2 N + 1)).biUnion (shellBad S) := by sorry

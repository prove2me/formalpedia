-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_fin_two_pow_inv_le_two
-- name    : CollatzEndpointTransport.FixedTotal.sum_fin_two_pow_inv_le_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:11:39.755+00:00
-- url     : https://prove2.me/theorems/a164e872-4a79-532d-aba7-fcb8cb38ac55
-- title:
--   Fixed Total: sum fin two pow inv le two
-- statement:
--   The geometric first-odd-position weights have total mass below two.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/SharpCentralRenyiPullback.lean#L744-L754
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/SharpCentralRenyiPullback.lean#L744-L754

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.sum_fin_two_pow_inv_le_two (M : ℕ) :
    (∑ u : Fin M, ((2 : ℝ) ^ (u : ℕ))⁻¹) ≤ 2 := by sorry

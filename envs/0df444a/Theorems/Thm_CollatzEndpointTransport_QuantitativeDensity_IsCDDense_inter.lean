-- Prove2me | Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_IsCDDense_inter
-- name    : CollatzEndpointTransport.QuantitativeDensity.IsCDDense.inter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:08:05.212696+00:00
-- url     : https://prove2.me/theorems/4cc86922-b46a-4f86-998d-657206572620
-- title:
--   Is CDDense: inter
-- statement:
--   Intersecting two good sets adds their prefactors and preserves a common
--   exponent.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/QuantitativeDensity.lean#L114-L142
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/QuantitativeDensity.lean#L114-L142

import Mathlib
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensity
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.QuantitativeDensity
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.QuantitativeDensity.IsCDDense.inter
    {S T : Set ℕ} {C₁ C₂ D : ℝ}
    (hS : IsCDDense S C₁ D) (hT : IsCDDense T C₂ D) :
    IsCDDense (S ∩ T) (C₁ + C₂) D := by sorry

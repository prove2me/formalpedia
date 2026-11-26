-- Prove2me | Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_IsCDDense_mono_set
-- name    : CollatzEndpointTransport.QuantitativeDensity.IsCDDense.mono_set
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:08:09.269938+00:00
-- url     : https://prove2.me/theorems/67f02ea1-2a70-42eb-b4ab-9e01fe8bb8e7
-- title:
--   Is CDDense: mono set
-- statement:
--   Passing to a larger good set preserves quantitative density.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/QuantitativeDensity.lean#L96-L110
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/QuantitativeDensity.lean#L96-L110

import Mathlib
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensity
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.QuantitativeDensity
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.QuantitativeDensity.IsCDDense.mono_set
    {S T : Set ℕ} {C D : ℝ} (h : IsCDDense S C D) (hST : S ⊆ T) :
    IsCDDense T C D := by sorry

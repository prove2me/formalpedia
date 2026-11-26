-- Prove2me | Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_mem_collatzPullback
-- name    : CollatzEndpointTransport.QuantitativeDensity.mem_collatzPullback
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:21:05.663076+00:00
-- url     : https://prove2.me/theorems/6c377198-9bf2-5c49-b2c0-195ef886c143
-- title:
--   Quantitative Density: mem collatz Pullback
-- statement:
--   The Quantitative Density construction uses the mem collatz Pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/QuantitativePullbackDefs.lean#L115-L117
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/QuantitativePullbackDefs.lean#L115-L117

import Definitions.Def_CollatzEndpointTransport_Common_AffineCorrectionDensity
import Definitions.Def_CollatzEndpointTransport_Common_TerrasInitialWindow
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativePullbackDefs
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.QuantitativeDensity
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.QuantitativeDensity.mem_collatzPullback {S : Set ℕ} {n : ℕ} :
    n ∈ collatzPullback S ↔ (Terras.T^[Nat.log 2 n]) n ∈ S := by sorry

-- Prove2me | Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_mem_basePullback
-- name    : CollatzEndpointTransport.QuantitativeDensity.mem_basePullback
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:21:39.979794+00:00
-- url     : https://prove2.me/theorems/9a5bfaa9-f3d2-409b-ae78-92dde5cddaf9
-- title:
--   Quantitative Density: mem base Pullback
-- statement:
--   The Quantitative Density construction uses the mem base Pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/QuantitativePullbackDefs.lean#L120-L122
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/QuantitativePullbackDefs.lean#L120-L122

import Definitions.Def_CollatzEndpointTransport_Common_AffineCorrectionDensity
import Definitions.Def_CollatzEndpointTransport_Common_TerrasInitialWindow
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativePullbackDefs
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.QuantitativeDensity
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.QuantitativeDensity.mem_basePullback {alpha : ℝ} {S : Set ℕ} {n : ℕ} :
    n ∈ basePullback alpha S ↔ baseMap alpha n ∈ S := by sorry

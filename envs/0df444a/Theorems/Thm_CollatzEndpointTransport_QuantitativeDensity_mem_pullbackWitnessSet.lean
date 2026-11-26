-- Prove2me | Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_mem_pullbackWitnessSet
-- name    : CollatzEndpointTransport.QuantitativeDensity.mem_pullbackWitnessSet
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:23:38.02218+00:00
-- url     : https://prove2.me/theorems/68c61d8f-198e-5daf-9c48-4f9b1866c89a
-- title:
--   Quantitative Density: mem pullback Witness Set
-- statement:
--   The Quantitative Density construction uses the mem pullback Witness Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/QuantitativePullbackDefs.lean#L124-L136
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/QuantitativePullbackDefs.lean#L124-L136

import Definitions.Def_CollatzEndpointTransport_Common_AffineCorrectionDensity
import Definitions.Def_CollatzEndpointTransport_Common_TerrasInitialWindow
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativePullbackDefs
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.QuantitativeDensity
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.QuantitativeDensity.mem_pullbackWitnessSet
    {S : Set ℕ} {eta etaPrime alpha correctionTol : ℝ} {n : ℕ} :
    n ∈ pullbackWitnessSet S eta etaPrime alpha correctionTol ↔
      baseMap alpha n ∈ coneCore 2 etaPrime S ∧
      n ∈ Terras.parityGood eta ∧
      n ∈ Terras.affineCorrectionGood correctionTol := by sorry

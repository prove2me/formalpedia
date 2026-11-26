-- Prove2me | Theorems.Thm_Auto_aux_integrable_of_memW0
-- name    : Auto.aux_integrable_of_memW0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:46:19.876851+00:00
-- url     : https://prove2.me/theorems/6bdadd30-e23a-4fe1-af54-b05fc1869e7b
-- title:
--   Auto: aux integrable of mem W0
-- statement:
--   Auxiliary fact extracting ordinary integrability from Wiener-space membership.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/ConvolutionAlongVector.lean#L104-L110
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/ConvolutionAlongVector.lean#L104-L110

module
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Definitions.Def_LeanNct_Auto_Preliminaries_ConvolutionAlongVector
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric
open scoped FourierTransform RealInnerProductSpace

theorem Auto.aux_integrable_of_memW0 {E 𝕜 : Type*} [NormedAddCommGroup E] [ProperSpace E]
    [MeasureSpace E] [BorelSpace E] [NormedAddCommGroup 𝕜]
    {f : E → 𝕜} (hf : MemW0 f) : Integrable f := by sorry

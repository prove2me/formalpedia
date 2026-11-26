-- Prove2me | Theorems.Thm_Auto_aux_memW0_integral_real
-- name    : Auto.aux_memW0_integral_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:53:40.994813+00:00
-- url     : https://prove2.me/theorems/c36816b3-f652-52f1-b20d-96c5e8faee10
-- title:
--   Auto: aux mem W0 integral real
-- statement:
--   Auxiliary fibre-integration closure result needed for convolution along a real direction.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/ConvolutionAlongVector.lean#L113-L150
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/ConvolutionAlongVector.lean#L113-L150

module
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Definitions.Def_LeanNct_Auto_Preliminaries_ConvolutionAlongVector
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric
open scoped FourierTransform RealInnerProductSpace

theorem Auto.aux_memW0_integral_real {n : ℕ}
    {𝕜 : Type*} [NormedField 𝕜] [NormedSpace ℝ 𝕜] [CompleteSpace 𝕜]
    {f : EuclideanSpace ℝ (Fin n) × ℝ → 𝕜} (hf : MemW0 f) :
    MemW0 (fun u ↦ ∫ p, f (u, p)) := by sorry

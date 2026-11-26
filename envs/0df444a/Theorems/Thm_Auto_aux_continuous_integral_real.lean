-- Prove2me | Theorems.Thm_Auto_aux_continuous_integral_real
-- name    : Auto.aux_continuous_integral_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:52:34.526281+00:00
-- url     : https://prove2.me/theorems/e3ac6e7e-1575-47db-be41-56e6be46b23c
-- title:
--   Auto: aux continuous integral real
-- statement:
--   Auxiliary dominated-convergence argument for the continuity of an integral over the real
--   coordinate of a Wiener-space function.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/ConvolutionAlongVector.lean#L65-L101
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/ConvolutionAlongVector.lean#L65-L101

module
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Definitions.Def_LeanNct_Auto_Preliminaries_ConvolutionAlongVector
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric
open scoped FourierTransform RealInnerProductSpace

theorem Auto.aux_continuous_integral_real {n : ℕ}
    {𝕜 : Type*} [NormedField 𝕜] [NormedSpace ℝ 𝕜] [CompleteSpace 𝕜]
    {f : EuclideanSpace ℝ (Fin n) × ℝ → 𝕜} (hf : MemW0 f) :
    Continuous (fun u ↦ ∫ p, f (u, p)) := by sorry

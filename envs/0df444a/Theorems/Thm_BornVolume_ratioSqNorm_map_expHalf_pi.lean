-- Prove2me | Theorems.Thm_BornVolume_ratioSqNorm_map_expHalf_pi
-- name    : BornVolume.ratioSqNorm_map_expHalf_pi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:52:43.433234+00:00
-- url     : https://prove2.me/theorems/90fd2d59-3de8-4ddd-a2da-ec64f68064f3
-- title:
--   Born Volume: ratio Sq Norm map exp Half pi
-- statement:
--   **Normalised exponentials are uniform on the simplex.** The free-coordinate ratio map
--   pushes the `N`-fold product `Exp(1/2)^{⊗N}` (`N = M+1`) to `M!` times Lebesgue measure
--   restricted to the open simplex: the Dirichlet(1,…,1) law. For `M = 1` it is the uniform law on
--   `(0,1)`.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/MomentRatioUniformN.lean#L401-L545
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/MomentRatioUniformN.lean#L401-L545

module
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.LinearAlgebra.Matrix.Block
public import Definitions.Def_BornVolumeLean_Volume_MomentMarginalUniform
public import Definitions.Def_BornVolumeLean_MeasureTheory_LintegralFintypeProd
public import Definitions.Def_BornVolumeLean_Volume_MomentRatioUniformN
set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory Real Set
open scoped ENNReal
open BornVolume
variable {M : ℕ}

theorem BornVolume.ratioSqNorm_map_expHalf_pi :
    Measure.map ratioN (Measure.pi (fun _ : Fin (M + 1) => expHalf))
      = (Nat.factorial M : ℝ≥0∞) • volume.restrict openSimplexFree := by sorry

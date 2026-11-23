-- Prove2me | Theorems.Thm_DedekindZeta_ConeRadialReduction_orbitTheta_inv_apply
-- name    : DedekindZeta.ConeRadialReduction.orbitTheta_inv_apply
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:50:27.466491+00:00
-- url     : https://prove2.me/theorems/fd4bbb19-a516-4c9f-9401-35925f1cc959
-- title:
--   Cone Radial Reduction: orbit Theta inv apply
-- statement:
--   **Norm-1 involution substitution for `orbitTheta`.** Substituting the
--   radius-`1/r` slice through the measure-preserving norm-1 involution `σ ↦ σ⁻¹`
--   (`surfaceMeasure`-preserving on `normEqOneSurface K`, since `N σ⁻¹ = 1`) together
--   with the radial identity `radialMap K (1/r) σ⁻¹ = (radialMap K r σ)⁻¹` rewrites
--   the `r ↦ 1/r` orbit theta as the surface integral of the *inverted* kernel
--   `Θ(𝔞, (radialMap K r σ)⁻¹)`. This isolates the geometric substitution underlying
--   the orbit inversion law (the standard treatment).
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L3002-L3120
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L3002-L3120

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_ConeRadialReduction
set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory Module
open scoped Real ENNReal nonZeroDivisors
open DedekindZeta DedekindZeta.ConeRadialReduction
variable (K : Type*) [Field K] [NumberField K]
variable {K}

theorem DedekindZeta.ConeRadialReduction.orbitTheta_inv_apply (𝔞 : Ideal (𝓞 K)) (r : ℝ) (hr : 0 < r) :
    orbitTheta K 𝔞 (1 / r)
      = ∫ σ in normEqOneSurface K,
          Theta.idealThetaKernel K 𝔞 (radialMap K r σ)⁻¹ ∂(surfaceMeasure K) := by sorry

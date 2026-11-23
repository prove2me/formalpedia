-- Prove2me | Theorems.Thm_DedekindZeta_ConeRadialReduction_continuousOn_orbitTheta
-- name    : DedekindZeta.ConeRadialReduction.continuousOn_orbitTheta
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:39:49.610434+00:00
-- url     : https://prove2.me/theorems/b2e5f54e-2c42-4003-b77c-0aec19ef1509
-- title:
--   Cone Radial Reduction: continuous On orbit Theta
-- statement:
--   **Continuity of the orbit-integrated radial theta** `r ↦ orbitTheta K 𝔞 r`
--   **on the open ray `(0, ∞)`**.
--
--   The statement is `ContinuousOn` over `Set.Ioi 0`, NOT global continuity: for
--   `σ ∈ normEqOneSurface K` (`mixedEmbedding.norm σ = 1`) the radial point
--   `radialMap K r σ` has `mixedEmbedding.norm = r` (`norm_radialMap_of_mem`), so it
--   lands in the Gaussian-summable nonzero-norm locus
--   `{x | mixedEmbedding.norm x ≠ 0}` — on which `Theta.idealThetaKernel` is
--   continuous (`Theta.continuousOn_idealThetaKernel`) — **exactly when `r > 0`**.
--   At `r ≤ 0` the integrand hits the zero-norm locus where the theta kernel is the
--   junk value `0`/non-summable, so `orbitTheta` is not continuous there.
--
--   The proof is the dominated-continuity argument for parametric integrals
--   (`continuousAt_of_dominated`) using the restricted (`Ioi 0`) kernel continuity
--   and the uniform Gaussian bound over the surface. the standard treatment.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L2000-L2120
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L2000-L2120

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
variable (K)

theorem DedekindZeta.ConeRadialReduction.continuousOn_orbitTheta (𝔞 : Ideal (𝓞 K)) :
    ContinuousOn (orbitTheta K 𝔞) (Set.Ioi 0) := by sorry

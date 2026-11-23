-- Prove2me | Theorems.Thm_DedekindZeta_ConeRadialReduction_continuousOn_orbitThetaFrac
-- name    : DedekindZeta.ConeRadialReduction.continuousOn_orbitThetaFrac
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:39:39.481847+00:00
-- url     : https://prove2.me/theorems/6f3dbd84-3d23-4423-87da-4caadaed44d5
-- title:
--   Cone Radial Reduction: continuous On orbit Theta Frac
-- statement:
--   **Continuity of the fractional orbit-integrated radial theta**
--   `r ↦ orbitThetaFrac K I r` **on the open ray `(0, ∞)`**, the dual-side analogue
--   of `continuousOn_orbitTheta` with `Theta.mixedThetaKernel K I` in place of
--   `Theta.idealThetaKernel K 𝔞`. Like the primal case this is `ContinuousOn`
--   `Set.Ioi 0`, not global: `radialMap K r σ` lands in the nonzero-norm
--   Gaussian-summable locus — on which `Theta.mixedThetaKernel` is continuous
--   (`Theta.continuousOn_mixedThetaKernel`) — exactly when `r > 0`. the standard treatment.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L1680-L1806
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L1680-L1806

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

theorem DedekindZeta.ConeRadialReduction.continuousOn_orbitThetaFrac (I : FractionalIdeal (𝓞 K)⁰ K) :
    ContinuousOn (orbitThetaFrac K I) (Set.Ioi 0) := by sorry

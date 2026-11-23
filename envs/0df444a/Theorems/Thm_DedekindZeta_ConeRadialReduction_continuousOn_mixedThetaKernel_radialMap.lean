-- Prove2me | Theorems.Thm_DedekindZeta_ConeRadialReduction_continuousOn_mixedThetaKernel_radialMap
-- name    : DedekindZeta.ConeRadialReduction.continuousOn_mixedThetaKernel_radialMap
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:31:30.295398+00:00
-- url     : https://prove2.me/theorems/5a0e64ea-3b33-4e6b-9915-071340353874
-- title:
--   Cone Radial Reduction: continuous On mixed Theta Kernel radial Map
-- statement:
--   **Continuity of the mixed theta kernel along the radius-`r` surface slice.**
--   For `r > 0`, `σ ↦ Theta.mixedThetaKernel K I (radialMap K r σ)` is continuous on
--   `closure (normEqOneSurface K)`: `radialMap K r` is continuous and maps the
--   closure into the nonzero-norm locus (`mapsTo_radialMap_closure_normEqOneSurface`),
--   on which `Theta.mixedThetaKernel K I` is continuous
--   (`Theta.continuousOn_mixedThetaKernel`).  The kernel is genuinely discontinuous
--   at `{N = 0}` (the Gaussian lattice sum diverges there), which is exactly why we
--   restrict to this slice where `N (radialMap K r σ) = r > 0`.  the standard treatment.
--   Reusable by `continuousOn_orbitThetaFrac` / `orbitTheta_isBigO_exp`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L1618-L1624
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L1618-L1624

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

theorem DedekindZeta.ConeRadialReduction.continuousOn_mixedThetaKernel_radialMap (I : FractionalIdeal (𝓞 K)⁰ K)
    (r : ℝ) (hr : 0 < r) :
    ContinuousOn (fun σ => Theta.mixedThetaKernel K I (radialMap K r σ))
      (closure (normEqOneSurface K)) := by sorry

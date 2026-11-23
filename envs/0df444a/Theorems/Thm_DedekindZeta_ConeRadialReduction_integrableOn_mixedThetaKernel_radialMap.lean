-- Prove2me | Theorems.Thm_DedekindZeta_ConeRadialReduction_integrableOn_mixedThetaKernel_radialMap
-- name    : DedekindZeta.ConeRadialReduction.integrableOn_mixedThetaKernel_radialMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:28:01.48986+00:00
-- url     : https://prove2.me/theorems/2dba8bfa-e04d-4066-b6bb-8dd3e6248242
-- title:
--   Cone Radial Reduction: integrable On mixed Theta Kernel radial Map
-- statement:
--   **Integrability of the dual kernel over the radius-`r` surface slice.** For
--   `r > 0` the integrand `σ ↦ Θ_mix(I, radialMap K r σ)` defining `orbitThetaFrac`
--   is integrable over the (relatively compact) norm-1 surface fundamental domain
--   against `surfaceMeasure K`. The surface measure of the (relatively compact)
--   norm-1 surface is finite (`measure_normEqOneSurface_lt_top`), so the constant
--   bound `C` from `exists_bound_mixedThetaKernel_radialMap` is integrable on the
--   restricted (finite) measure; the integrand is `AEStronglyMeasurable` because it
--   is `ContinuousOn` the closure (`continuousOn_mixedThetaKernel_radialMap`), hence
--   on `normEqOneSurface K`.  Conclude via `Integrable.mono'`.  the standard treatment.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L1653-L1670
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L1653-L1670

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

theorem DedekindZeta.ConeRadialReduction.integrableOn_mixedThetaKernel_radialMap
    (I : FractionalIdeal (𝓞 K)⁰ K) (r : ℝ) (hr : 0 < r) :
    IntegrableOn (fun σ => Theta.mixedThetaKernel K I (radialMap K r σ))
      (normEqOneSurface K) (surfaceMeasure K) := by sorry

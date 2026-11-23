-- Prove2me | Theorems.Thm_DedekindZeta_ConeRadialReduction_radialIntegral_eq_mellin
-- name    : DedekindZeta.ConeRadialReduction.radialIntegral_eq_mellin
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:48:44.631833+00:00
-- url     : https://prove2.me/theorems/d5bb1733-fde4-457f-9a1a-992fe7edd2c9
-- title:
--   Cone Radial Reduction: radial Integral eq mellin
-- statement:
--   **The radial Mellin is Mathlib's `mellin` of `F`.** Since for `r > 0`,
--   `(r : ℂ)^s · r⁻¹ = (r : ℂ)^(s-1)`, the radial integral
--   `∫_0^∞ F(𝔞,r)·r^s · r⁻¹ dr` is exactly `mellin (orbitTheta K 𝔞) s`
--   (`= ∫_0^∞ (r:ℂ)^(s-1) • F(𝔞,r) dr`). This is the `reducedMellin`-shaped spelling
--   (`y^s dy/y = y^{s-1} dy`) of `DedekindZeta/MellinPrinciple.lean`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L912-L921
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L912-L921

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

theorem DedekindZeta.ConeRadialReduction.radialIntegral_eq_mellin (𝔞 : Ideal (𝓞 K)) (s : ℂ) :
    ∫ r in Set.Ioi (0 : ℝ),
        orbitTheta K 𝔞 r * (r : ℂ) ^ s * (r : ℝ)⁻¹ ∂volume
      = mellin (orbitTheta K 𝔞) s := by sorry

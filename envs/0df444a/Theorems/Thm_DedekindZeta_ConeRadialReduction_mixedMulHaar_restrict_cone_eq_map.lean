-- Prove2me | Theorems.Thm_DedekindZeta_ConeRadialReduction_mixedMulHaar_restrict_cone_eq_map
-- name    : DedekindZeta.ConeRadialReduction.mixedMulHaar_restrict_cone_eq_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:48:24.581635+00:00
-- url     : https://prove2.me/theorems/4d42de81-f030-43e0-8592-d972f086d014
-- title:
--   Cone Radial Reduction: mixed Mul Haar restrict cone eq map
-- statement:
--   **Measure-level form of the cone decomposition.** The cone-restricted Haar
--   measure `mixedMulHaar K` is the pushforward, along the radial parametrisation
--   `(r, σ) ↦ radialMap K r σ`, of the multiplicative-Haar weighted product measure
--   `(volume.restrict (0,∞)) ⊗ μ_S` with density `dr/r` (`ofReal r⁻¹`):
--
--       (mixedMulHaar K).restrict cone
--         = map (uncurry radialMap) (((vol|_{(0,∞)}) ⊗ μ_S).withDensity (ofReal ·.1⁻¹)) .
--
--   This is the measure-equality repackaging of the Lebesgue identity
--   `setLIntegral_cone_eq_radial`: two measures whose `lintegral` against every
--   measurable `ℝ≥0∞`-valued function agree are equal, and the iterated
--   `lintegral` on the right of `setLIntegral_cone_eq_radial` is, by Tonelli, the
--   `lintegral` of `h ∘ radialMap` against this pushforward. It is the bridge that
--   lets the Bochner (`ℂ`-valued) form `setIntegral_cone_eq_radial` be obtained by
--   `integral_map` + Fubini. Faithful to the standard treatment.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L750-L789
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L750-L789

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

theorem DedekindZeta.ConeRadialReduction.mixedMulHaar_restrict_cone_eq_map :
    (DedekindZeta.mixedMulHaar K).restrict (mixedEmbedding.fundamentalCone K)
      = Measure.map (fun p : ℝ × mixedSpace K => radialMap K p.1 p.2)
          (((volume.restrict (Set.Ioi (0 : ℝ))).prod (surfaceMeasure K)).withDensity
            (fun p => ENNReal.ofReal p.1⁻¹)) := by sorry

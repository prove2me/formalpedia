-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_coord9_turn7_original_singular_geometric_generator_profile
-- name    : AvramDividend.Classical.avram_coord9_turn7_original_singular_geometric_generator_profile
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T23:28:31.29134+00:00
-- url     : https://prove2.me/theorems/d3319180-9ed1-4af8-939b-03ff298a997b
-- title:
--   Exact original singular Lévy generator at a geometric post-dividend reserve
-- statement:
--   For the actual Avram bounded-variation Levy source with the singular absolutely continuous negative jump measure and zero canonical drift coefficient, a dyadic positive post-dividend reserve has the explicit nonintegrable affine generator profile. The theorem is conditional on the exact reserve identification.
-- source:
--   Original-generator exact identity 24cc445a, with the source reserve and Mathlib half-power conversion.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_a19_affine_singular_subunit_original_generator_eq
open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual singular-density original generator evaluated at a geometric
    post-dividend reserve has the exact signed scalar HJB profile. -/

theorem AvramDividend.Classical.avram_coord9_turn7_original_singular_geometric_generator_profile
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hν : X.ν = volume.withDensity (fun z : ℝ =>
      if z ∈ Ioo (-1 : ℝ) 0
      then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0))
    (hc : X.c = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (K : Ω → ℕ) (y : ℕ → ℝ)
    (hy : ∀ k, 0 < y k) (hsmall : ∀ k, y k ≤ 1 / 16)
    (hreserve : ∀ ω, x - rightLimit D 0 ω = y (K ω)) :
    ∀ ω, X.generator
        (fun u : ℝ => if u < 0 then (0 : ℝ) else 1 + u)
        (x - rightLimit D 0 ω) -
      (if x - rightLimit D 0 ω < 0 then (0 : ℝ)
        else 1 + (x - rightLimit D 0 ω)) =
      (3 : ℝ) + y (K ω) - 4 * Real.sqrt (y (K ω)) -
        2 / Real.sqrt (y (K ω)) := by sorry

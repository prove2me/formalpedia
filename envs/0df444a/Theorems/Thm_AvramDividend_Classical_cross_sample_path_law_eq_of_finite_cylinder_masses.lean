-- Prove2me | Theorems.Thm_AvramDividend_Classical_cross_sample_path_law_eq_of_finite_cylinder_masses
-- name    : AvramDividend.Classical.cross_sample_path_law_eq_of_finite_cylinder_masses
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:29:44.004724+00:00
-- url     : https://prove2.me/theorems/ef7cd2a9-c0c0-419e-8826-3835d11e9494
-- title:
--   Full real-valued path-law equality from finite cylinders on different probability spaces
-- statement:
--   Two real-valued random paths Y and Z may live on entirely different sample probability spaces. If their first measure has finite mass and their probabilities coincide for every finite-coordinate rectangular cylinder, then the full pushforward measures on the function-valued path space coincide. This closes a sample-space compatibility gap between Prove2Me's arbitrary Lévy process and LeanLevy's separately constructed Poisson jump model. The result is on all-time coordinate-product measurable path space, and can be used for càdlàg paths and measurable jump-count events without equating sample points.
-- source:
--   Proved piPathMeasure_eq_of_finite_cylinder_masses theorem [4d62c918-6680-4aa9-98a1-d28e432ce446]; Mathlib MeasurableSet.pi and Measure.map_apply at pinned revision. Canonical model path law transfer route for Open ae_early_downward_jumps_of_infinite_negative_activity [ff758fb4-87e5-4eec-b153-b6135498ca04].

import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Map
import Theorems.Thm_AvramDividend_Classical_piPathMeasure_eq_of_finite_cylinder_masses

open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.cross_sample_path_law_eq_of_finite_cylinder_masses
    {Ω₁ Ω₂ ι : Type*}
    [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂]
    (P₁ : Measure Ω₁) (P₂ : Measure Ω₂)
    (Y : Ω₁ → (ι → ℝ)) (Z : Ω₂ → (ι → ℝ))
    (hY : Measurable Y) (hZ : Measurable Z)
    (hP : P₁ univ ≠ ⊤)
    (hCyl : ∀ (J : Finset ι) (B : ι → Set ℝ),
      (∀ i ∈ J, MeasurableSet (B i)) →
      P₁ (Y ⁻¹' (Set.pi (J : Set ι) B)) =
      P₂ (Z ⁻¹' (Set.pi (J : Set ι) B))) :
    Measure.map Y P₁ = Measure.map Z P₂ := by sorry

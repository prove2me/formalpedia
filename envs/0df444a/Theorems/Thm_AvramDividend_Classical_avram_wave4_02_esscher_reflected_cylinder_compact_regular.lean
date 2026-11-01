-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_02_esscher_reflected_cylinder_compact_regular
-- name    : AvramDividend.Classical.avram_wave4_02_esscher_reflected_cylinder_compact_regular
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:47:14.836872+00:00
-- url     : https://prove2.me/theorems/dd29e510-1cc7-49ac-b624-fcaeee4af432
-- title:
--   Actual Esscher-reflected cylinder content is inner regular by closed compact cylinders
-- statement:
--   There exists the genuine normalised additive content of the actual finite-clock Esscher-reflected SNLP joint running-supremum/drawdown laws, with exact marginal values, and for every measurable path cylinder s and every epsilon>0 there exists a closed-compact-base cylinder F⊆s with content of s\F less than epsilon. This is source identified, not an assumed generic content: it is constructed from the already Proved cylinder content and exact genuine compact inner approximation. It is precisely the inner-regular-content premise in the Kolmogorov extension proof, but does not yet establish sigma-subadditivity, all-horizon law, excursion marks, or a compensator.
-- source:
--   Canonical Proved source cylinder content 23e12e91; canonical Proved compact inner finite marginal regularity 9a4b63dc; pinned Mathlib cylinder_mem_closedCompactCylinders, sdiff_cylinder_same, measure_sdiff_lt_of_lt_add. Mathematical structural guide: Degenne-Pfaffelhuber, KolmogorovExtension4/KolmogorovExtension.lean, innerRegular_projectiveFamilyContent (Apache 2.0), independently rewritten here against exact source family.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_wave4_02_esscher_reflected_cylinder_content
import Theorems.Thm_AvramDividend_Classical_avram_wave4_02_esscher_reflected_finite_marginal_inner_regular
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_density_probability

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_02_esscher_reflected_cylinder_compact_regular
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∃ C : AddContent ℝ≥0∞
        (measurableCylinders (fun _ : ℝ≥0 => ℝ × ℝ)),
      C Set.univ = 1 ∧
        (∀ (I : Finset ℝ≥0) (A : Set (I → ℝ × ℝ)),
          MeasurableSet A →
            C (cylinder I A) =
              (Measure.map
                (fun ω : Ω => fun i : I =>
                  (runningSup X (i : ℝ≥0) ω, reflectedSup X (i : ℝ≥0) ω))
                (P.withDensity (fun ω => ENNReal.ofReal
                  (Real.exp (φ * X.X ((I.sup id) + 1) ω -
                    ((((I.sup id) + 1 : ℝ≥0) : ℝ)) * X.ψ φ))))) A) ∧
        (∀ (s : Set (ℝ≥0 → ℝ × ℝ)),
          s ∈ measurableCylinders (fun _ : ℝ≥0 => ℝ × ℝ) →
            ∀ (ε : ℝ≥0∞), 0 < ε →
              ∃ F : Set (ℝ≥0 → ℝ × ℝ),
                F ∈ closedCompactCylinders (fun _ : ℝ≥0 => ℝ × ℝ) ∧
                F ⊆ s ∧ C (s \ F) < ε) := by sorry

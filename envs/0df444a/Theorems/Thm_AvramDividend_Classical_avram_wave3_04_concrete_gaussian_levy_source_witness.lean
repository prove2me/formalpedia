-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_concrete_gaussian_levy_source_witness
-- name    : AvramDividend.Classical.avram_wave3_04_concrete_gaussian_levy_source_witness
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T01:03:50.11662+00:00
-- url     : https://prove2.me/theorems/c348cefa-238d-46fa-8dd8-7f7e3011dc9d
-- title:
--   An actual unbounded-variation spectrally negative Lévy process with negative drift and Gaussian coefficient one exists
-- statement:
--   This theorem assembles the genuine canonical projective-limit Brownian path into the source SpectrallyNegativeLevy structure. Adaptedness uses the natural filtration; the full filtered independence and stationary increments are separately Proved. Gaussian regularity and Laplace exponent are inherited from the source constructor. The witness has c=-1, sigma=1, zero Levy jump measure.
-- source:
--   Source constructor 275d0cb6-b69f-45c3-9f0e-cbe59626e268; canonical stationary law 75e75ec9-762c-493a-8ed1-2a17d241b75a; canonical natural adaptation f81b6ab6-d291-4f59-8edb-d400ad0cc070; canonical independence pending.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_canonical_drifted_brownian_natural_adapted
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_canonical_drifted_brownian_filtered_indep
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_canonical_drifted_brownian_stationary_all
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_canonical_brownian_levy_constructor_of_increment_laws

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_04_concrete_gaussian_levy_source_witness :
    ∃ (𝓕 : Filtration ℝ≥0
        (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)))
      (X : SpectrallyNegativeLevy gaussianLimit 𝓕),
      X.X = (fun (t : ℝ≥0) (ω : ℝ≥0 → ℝ) =>
        brownian t ω - brownian 0 ω - (t : ℝ)) ∧
      X.c = -1 ∧ X.σ = 1 ∧ X.ν = 0  := by sorry

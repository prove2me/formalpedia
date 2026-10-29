-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_cr_new_finite_killed_geometric_potential_exact_mass_laplace
-- name    : AvramDividend.Classical.avram_ws01e_cr_new_finite_killed_geometric_potential_exact_mass_laplace
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T23:37:11.012445+00:00
-- url     : https://prove2.me/theorems/9f7bf7a2-e2be-4cab-9092-720e6bedc948
-- title:
--   Exact killed geometric-renewal total mass and raw Laplace transform at every positive rate
-- statement:
--   A finite positive-height jump kernel κ with total mass strictly less than finite δ admits one explicit positive killed renewal-potential measure β. The result gives the exact finite mass β(ℝ)=δ⁻¹(1−δ⁻¹κ(ℝ))⁻¹, no negative support and its ordinary positive Laplace transform at all s>0. This extends the already Proved generic cumulative-renewal theorem by exposing the two facts required by the accepted uniform-tightness and weak-limit theorems. Construct β as a geometric sum of additive convolution powers of κ and use accepted exact mass/transform proofs.
-- source:
--   Pinned accepted exists_sfinite_convolution_power_sequence, additive_convolution_powers_mass, finite_positive_geometric_measure_sum_of_mass_powers, positiveLaplace_convolution_powers, positiveLaplace_geometric_measure_sum. Distinct additional exact mass plus raw all-s Laplace interface needed for compound-Poisson drift/jump truncations in the unbounded Esscher scale cumulative representation.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_exists_sfinite_convolution_power_sequence
import Theorems.Thm_AvramDividend_Classical_additive_convolution_powers_mass
import Theorems.Thm_AvramDividend_Classical_finite_positive_geometric_measure_sum_of_mass_powers
import Theorems.Thm_AvramDividend_Classical_positiveLaplace_convolution_powers
import Theorems.Thm_AvramDividend_Classical_positiveLaplace_geometric_measure_sum
open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_ws01e_cr_new_finite_killed_geometric_potential_exact_mass_laplace
    (κ : Measure ℝ) [SFinite κ] (hκsupp : κ (Iio (0 : ℝ)) = 0)
    (δ : ℝ≥0∞) (hδ : 0 < δ) (hδfin : δ ≠ ⊤)
    (hgap : κ Set.univ < δ) :
    ∃ β : Measure ℝ,
      β Set.univ = δ⁻¹ * (1 - δ⁻¹ * κ Set.univ)⁻¹ ∧
      β (Iio (0 : ℝ)) = 0 ∧
      ∀ s : ℝ, 0 < s →
        (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-s * x)) ∂β) =
          δ⁻¹ * (1 - δ⁻¹ *
            (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-s * z)) ∂κ))⁻¹ := by sorry

-- Prove2me | Theorems.Thm_AvramDividend_Classical_geometric_renewal_explicit_powers_laplace_ac
-- name    : AvramDividend.Classical.geometric_renewal_explicit_powers_laplace_ac
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T18:16:35.271785+00:00
-- url     : https://prove2.me/theorems/8ff61126-5543-4bed-b979-d06d47e39754
-- title:
--   Finite absolutely continuous geometric renewal measure with explicit convolution-power witness
-- statement:
--   Strengthen the canonically Proved geometric-renewal construction by retaining the exact SFinite convolution powers m_n, their recurrence, and the equality β = Σ_n δ^(-n-1) m_n, alongside finite total mass, support on the nonnegative axis, positive-halfline absolute continuity and the all-parameter cumulative Laplace identity. This is the precise witness equality required to combine the BV Esscher finite-Laplace proof with the already Proved real convolution-series density theorem and thereby solve the scale identification child 1ca4a724-85b7-48bf-bae4-37890ef7055b.
-- source:
--   Exact witness-preserving strengthening of the canonically Proved positive_finite_supported_geometric_renewal_uniform_ac proof (491f9930-03d5-45ba-a255-5761616ef2dd), keeping m, β, their recurrence and the geometric measure sum equation.

import Theorems.Thm_AvramDividend_Classical_exists_sfinite_convolution_power_sequence
import Theorems.Thm_AvramDividend_Classical_additive_convolution_powers_mass
import Theorems.Thm_AvramDividend_Classical_finite_positive_geometric_measure_sum_of_mass_powers
import Theorems.Thm_AvramDividend_Classical_positiveLaplace_convolution_powers
import Theorems.Thm_AvramDividend_Classical_positiveLaplace_geometric_measure_sum
import Theorems.Thm_AvramDividend_Classical_positiveLaplace_cumulative_measure
import Theorems.Thm_AvramDividend_Classical_nonnegative_halfline_support_of_measure_convolution
import Theorems.Thm_AvramDividend_Classical_geometric_convolution_renewal_positive_part_ac
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Data.ENNReal.Inv
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.geometric_renewal_explicit_powers_laplace_ac
    (κ : Measure ℝ) [SFinite κ]
    (hκsupp : κ (Iio (0 : ℝ)) = 0)
    (hκac : κ ≪ (volume : Measure ℝ))
    (δ : ℝ≥0∞) (hδ : 0 < δ) (hδfin : δ ≠ ⊤)
    (hgap : κ Set.univ < δ) :
    ∃ (m : ℕ → Measure ℝ) (β : Measure ℝ),
      m 0 = Measure.dirac (0 : ℝ) ∧
      (∀ n : ℕ, m (n + 1) = κ.conv (m n)) ∧
      (∀ n : ℕ, SFinite (m n)) ∧
      β = Measure.sum (fun n : ℕ => (δ⁻¹) ^ (n + 1) • m n) ∧
      0 < β Set.univ ∧ β Set.univ ≠ ⊤ ∧
      β (Iio (0 : ℝ)) = 0 ∧
      β.restrict (Ioi (0 : ℝ)) ≪ (volume : Measure ℝ) ∧
      (∀ x : ℝ, β (Iic x) ≠ ⊤) ∧
      (∀ s : ℝ, 0 < s →
        (∫⁻ x : ℝ in Ioi 0,
          ENNReal.ofReal (Real.exp (-s * x)) * β (Iic x)) =
        ENNReal.ofReal (1 / s) *
          (δ⁻¹ * (1 - δ⁻¹ *
            (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-s * z)) ∂κ))⁻¹)) := by sorry

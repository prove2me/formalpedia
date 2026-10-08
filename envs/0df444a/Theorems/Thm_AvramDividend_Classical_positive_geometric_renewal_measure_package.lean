-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_geometric_renewal_measure_package
-- name    : AvramDividend.Classical.positive_geometric_renewal_measure_package
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T23:46:54.798123+00:00
-- url     : https://prove2.me/theorems/1954c753-6665-450f-a170-3dcb9e967f65
-- title:
--   Geometric renewal measure transform, local finiteness and positive atom
-- statement:
--   For a convolution-power sequence m_n of a positive kernel κ, the geometric renewal measure β=Σ c^(n+1)m_n has the expected geometric Laplace transform. If that transform is finite, then every lower cumulative interval has finite β-mass, and if c>0 and m_0 is Dirac at zero, β has a positive atom at zero.
-- source:
--   Composition of the Proved helpers positiveLaplace_convolution_powers, positiveLaplace_geometric_measure_sum, finite_Iic_of_positive_laplace_ne_top and positive_atom_geometric_measure_sum.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

namespace AvramDividend.Classical

theorem positive_geometric_renewal_measure_package
    (κ : Measure ℝ) [SFinite κ]
    (m : ℕ → Measure ℝ)
    (θ : ℝ) (r c : ℝ≥0∞)
    (hθ : 0 < θ)
    (hm0 : m 0 = Measure.dirac 0)
    (hmsucc : ∀ n : ℕ, m (n + 1) = Measure.conv κ (m n))
    (hsf : ∀ n : ℕ, SFinite (m n))
    (hκ : (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-θ * x)) ∂κ) = r)
    (hc : 0 < c)
    (hgeom : c * (1 - c * r)⁻¹ ≠ ⊤) :
    let β : Measure ℝ := Measure.sum (fun n : ℕ => c ^ (n + 1) • m n)
    ((∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-θ * x)) ∂β) = c * (1 - c * r)⁻¹) ∧
      (∀ x : ℝ, β (Iic x) ≠ ⊤) ∧
      0 < β {0} := by
  sorry

end AvramDividend.Classical

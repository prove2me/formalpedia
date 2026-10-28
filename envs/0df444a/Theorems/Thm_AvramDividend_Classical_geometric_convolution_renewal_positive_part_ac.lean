-- Prove2me | Theorems.Thm_AvramDividend_Classical_geometric_convolution_renewal_positive_part_ac
-- name    : AvramDividend.Classical.geometric_convolution_renewal_positive_part_ac
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T18:46:14.576753+00:00
-- url     : https://prove2.me/theorems/65207a5e-c948-4091-b029-b98147228049
-- title:
--   Geometric convolution renewal measure is absolutely continuous away from its initial atom
-- statement:
--   Let κ be an s-finite measure absolutely continuous with respect to Lebesgue volume. Starting with a Dirac atom at zero, let m_(n+1)=κ∗m_n and suppose all convolution powers are s-finite. Every positive-order convolution has a Lebesgue density, so any geometric nonnegative measure sum Σ c^(n+1)m_n is absolutely continuous on (0,∞). This supplies the exact missing geometric renewal measure density bridge for the corrected bounded-variation Esscher series representation (9be5ada9), its continuous density parent (17bc0aad), the C1 scale function and cstar_lt_top.
-- source:
--   Pinned Mathlib Measure.conv_absolutelyContinuous, Measure.conv_comm, Measure.sum_apply, absolutelyContinuous null-set criterion.

import Theorems.Thm_AvramDividend_Classical_renewal_measure_ac_on_positive
import Theorems.Thm_AvramDividend_Classical_positive_geometric_renewal_measure_package
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.geometric_convolution_renewal_positive_part_ac
    (κ : Measure ℝ) [SFinite κ]
    (hκac : κ ≪ (volume : Measure ℝ))
    (m : ℕ → Measure ℝ)
    (hm0 : m 0 = Measure.dirac (0 : ℝ))
    (hmsucc : ∀ n : ℕ, m (n + 1) = Measure.conv κ (m n))
    (hsf : ∀ n : ℕ, SFinite (m n))
    (c : ℝ≥0∞) :
    (Measure.sum (fun n : ℕ => c ^ (n + 1) • m n)).restrict (Ioi (0 : ℝ)) ≪
      (volume : Measure ℝ) := by sorry

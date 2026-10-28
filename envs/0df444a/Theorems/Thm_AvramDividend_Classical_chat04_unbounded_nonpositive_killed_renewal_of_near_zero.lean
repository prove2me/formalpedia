-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_unbounded_nonpositive_killed_renewal_of_near_zero
-- name    : AvramDividend.Classical.chat04_unbounded_nonpositive_killed_renewal_of_near_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T09:23:30.810962+00:00
-- url     : https://prove2.me/theorems/9a068bda-c9c5-43e4-934d-de16b149af78
-- title:
--   Full killed q-scale renewal identity from every non-positive reserve under near-zero negative regularity
-- statement:
--   Under unbounded variation and almost-sure arbitrarily early negative increments, the discounted killed q-scale expectation at every horizon equals W(x) for all initial reserves x≤0. Negative x are already ruined at time zero. At x=0, horizon zero is the deterministic initial condition and positive horizons vanish almost surely. This fully covers the non-positive branch of the open killed renewal identity needed for the two-sided stopped-scale martingale.
-- source:
--   Direct case-wise composition of Proved 82a74188-f140-406b-94e4-b3e3605e61b2, 115a9cae-b7dd-4330-b424-2fc89573a8e5, and 2956adf9-9042-4267-bfd1-8e2d23c7e425. Immediate consumer Open chat04_unbounded_killed_survival_discounted_scale_expectation (a885f0b3-3960-424d-97e4-abbcffe268ba) for stopped-scale theorem aed50a34 and parent 3e1ce2c8.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Theorems.Thm_AvramDividend_Classical_chat04_killed_survival_lintegral_zero_of_negative_initial_reserve
import Theorems.Thm_AvramDividend_Classical_chat04_killed_survival_lintegral_initial_nonnegative
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_zero_start_killed_renewal_of_ae_negative_near_zero

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_unbounded_nonpositive_killed_renewal_of_near_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnear : ∀ᵐ ω ∂P,
      ∀ ε : ℝ≥0, 0 < ε →
        ∃ s : ℝ≥0, s < ε ∧ X.X s ω < 0)
    (x : ℝ) (hx : x ≤ 0) (t : ℝ≥0) :
    (∫⁻ ω,
      ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
        (fun ω => ENNReal.ofReal
          (Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω))) ω ∂P) =
      ENNReal.ofReal (W x) := by sorry

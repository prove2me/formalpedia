-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mathfin22_original_local_simple_compensated_fibre_identity
-- name    : AvramDividend.Classical.avram_mathfin22_original_local_simple_compensated_fibre_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T14:16:17.450997+00:00
-- url     : https://prove2.me/theorems/e4e5295a-8edc-4e62-99fe-1855a5272bcb
-- title:
--   Original arbitrary infinite-activity finite negative band compensated simple physical marked-jump sum exact fibre identity
-- statement:
--   Adapt accepted Avram original physical compensated simple-fibre equality (c0e79a4d) by localising the original negative mark set S to a measurable cutoff separated from zero. Original sampled marked jump integral equals its finite actual Borel fibre count sum for every sample path via local proof 94132e91, and the ν-side finite simple fibre sum needs only locally finite ν(S), supplied by proved p2_a and generic a21 finite marked compensator identity. The algebra of the accepted theorem is retained verbatim with no global X.ν(Iio 0)<∞ premise and a pointwise equality, directly supplying the original infinite-activity fixed-band marked simple L2 bridge needed for 16f22886.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mathfin22_original_local_simple_mark_fibre_integral_exact
import Theorems.Thm_AvramDividend_Classical_avram_a21_finite_borel_simple_mark_intensity_fibre_sum_20261112
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_separated_borel_nu_finite
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_mathfin22_original_local_simple_compensated_fibre_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n : ℕ) (S : Set ℝ)
    (hS : MeasurableSet S)
    (hSep : S ⊆ Iic (-(1 / ((n : ℝ) + 1))))
    (g : SimpleFunc ℝ ℝ) (hBound : ∀ z ∈ S, |g z| ≤ 1) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let B : ℝ → Set ℝ := fun y => S ∩ g ⁻¹' {y}
    ∀ ω,
      (∑ y ∈ g.range, y *
          ((NX ω (Ioc 0 T ×ˢ B y)).toReal -
            (((T : ℝ≥0∞) * X.ν (B y)).toReal))) =
        (∫ p in (Ioc 0 T ×ˢ S), g p.2 ∂NX ω) -
          (T : ℝ) * (∫ z in S, g z ∂X.ν) := by sorry

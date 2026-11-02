-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_01_bv_original_future_marked_event_measure_finite
-- name    : AvramDividend.Classical.avram_wave6_01_bv_original_future_marked_event_measure_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T23:00:40.12803+00:00
-- url     : https://prove2.me/theorems/842335bc-bf3a-4496-b869-6b6d58aef328
-- title:
--   Original BV finite-activity marked jump count induces a finite measure in the past-event variable
-- statement:
--   For the given original SpectrallyNegativeLevy P 𝓕 under bounded variation and finite total negative jump intensity, for any finite time interval (s,t] and arbitrary Borel mark B, construct the finite measure Q_{s,t;B} on unchanged Ω whose value Q(A) is the expectation of the genuine sample-path jump count N_X((s,t]×B) restricted to any measurable event A. Finite total mass follows from monotonicity of actual counting measures and the canonically Proved all-time original fullmark rate (t-s)ν((−∞,0)). This supplies a finite source weighted history measure for π–λ independence arguments, without assuming factorisation by P(A) or the arbitrary-mark ν(B) law.
-- source:
--   Apply original event-weighted source measure existence 8efd34b1 and bound its total mass by the original fullmark expected count theorem 2fdbada6. No proxy and no assumed compensator.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_event_weighted_jump_count_is_measure
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_bv_original_fullmark_all_time_intervals_exact_rate
open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_01_bv_original_future_marked_event_measure_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B) :
    ∃ Q : Measure Ω,
      Q Set.univ < ⊤ ∧
      ∀ A : Set Ω, MeasurableSet A →
        Q A = (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ B) ∂P) := by sorry

-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_disjoint_nojump_intervals_independent
-- name    : AvramDividend.Classical.avram_wave4_04a_bv_actual_disjoint_nojump_intervals_independent
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T17:08:30.540333+00:00
-- url     : https://prove2.me/theorems/224f9dd8-6f1c-49c9-8ed2-6057b4ed8d69
-- title:
--   Actual finite-activity Lévy nojump events in ordered disjoint intervals are independent on original probability space
-- statement:
--   For the actual original finite-activity BV spectrally negative Lévy X and deterministic ordered intervals (s,t] and (u,v] with s≤t≤u≤v, probability of simultaneous absence of genuine source jumps factors into the product of the two probabilities. This is a finite-dimensional Poisson void-event independence property on the original Ω and right-continuous source filtration, derived by a.e. nojump/source-increment identification and actual right-continuous past independence. No constructed equal-law Lévy process and no full source count law asserted.
-- source:
--   Canonical Proved a31bfa74-a.e. original nojump equals drift source increment; canonically Proved b8ae0e83 original rightCont past nojump factor. The earlier source increment equality event is measurable in 𝓕.rightCont u by X.adapted and monotonicity. Transfer factorization through P-a.e. equality using Mathlib measure_congr.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04a_bv_actual_disjoint_nojump_intervals_independent
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (s t u v : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u) (huv : u ≤ v) :
    P ({ω : Ω | ∀ r : ℝ≥0, r ∈ Ioc s t →
      X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r = 0} ∩
       {ω : Ω | ∀ r : ℝ≥0, r ∈ Ioc u v →
        X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r = 0}) =
      P {ω : Ω | ∀ r : ℝ≥0, r ∈ Ioc s t →
        X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r = 0} *
      P {ω : Ω | ∀ r : ℝ≥0, r ∈ Ioc u v →
        X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r = 0} := by sorry

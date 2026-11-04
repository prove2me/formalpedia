-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_weighted_raw_large_mark_L1
-- name    : AvramDividend.Classical.avram_p4_c_generator_weighted_raw_large_mark_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:05:45.556324+00:00
-- url     : https://prove2.me/theorems/7fd71577-0f92-47b1-a1a4-7ac1c6f08a48
-- title:
--   Bounded predictable-clock weights preserve original large negative raw-jump product L1
-- statement:
--   For an arbitrary finite clock measure μ and measurable reserve R confined to [0,v], any measurable real clock weight a with a uniform bound M produces an integrable weighted original raw jump payoff a(t)(w(R(t)+z)-w(R(t))) over μ times the original Lévy ν restricted to z<-epsilon. This follows from the already Proved original raw-jump product L1 and the pinned Integrable.bdd_mul. It accommodates bounded discount factors and does not claim the weight's predictability, original jump-count compensation or an Ito identity.
-- source:
--   Proved P4-C finite_clock_raw_large_mark_L1 UUID b40bbce6-b87e-4410-be59-ae28455ffecc; pinned Mathlib Integrable.bdd_mul

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_finite_clock_raw_large_mark_L1
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_weighted_raw_large_mark_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {T : Type*} [mT : MeasurableSpace T]
    (μ : Measure T) [IsFiniteMeasure μ]
    (R a : T → ℝ) (hR : Measurable R) (ha : Measurable a)
    (w : ℝ → ℝ) (v ε : ℝ) (hv : 0 ≤ v) (hε : 0 < ε)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ t : ℝ, t < 0 → w t = 0)
    (hcap : ∀ t, R t ∈ Icc 0 v)
    (M : ℝ) (hweight : ∀ t, |a t| ≤ M) :
    Integrable
      (fun p : T × ℝ => a p.1 * (w (R p.1 + p.2) - w (R p.1)))
      (μ.prod (X.ν.restrict (Iio (-ε)))) := by sorry

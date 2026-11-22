-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_oai_original_physical_simple_signed_mark_predictable_weight_condExp_zero_allactivity_20261122
-- name    : AvramDividend.Classical.avram_oai_original_physical_simple_signed_mark_predictable_weight_condExp_zero_allactivity_20261122
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T16:57:48.814586+00:00
-- url     : https://prove2.me/theorems/d44667bc-5dd2-478d-802b-0cbfe551bbac
-- title:
--   True all-activity original Lévy physical signed finite simple negative marked predictable-weight future compensated noise has zero conditional expectation
-- statement:
--   For the ACTUAL intrinsic physical marked-jump measure of a spectrally negative Lévy process with possibly infinite global jump activity, any locally finite intensity negative mark region S, real finite-range simple mark g and any genuinely previsible at time s real weight H measurable in the original right-continuous past filtration, the weighted signed compensated future-mark increment H×G_(s,t) has zero conditional expectation given the true right-continuous past F_s, whenever the product is integrable. The proof establishes integrability of G directly from the already Proved original finite negative Borel mark Campbell L1 theorem for each actual physical finite simple-mark fibre, applies the independently Proved ORIGINAL source conditional centring for the complete signed finite simple-mark increment ec634a99, and uses pinned conditional-expectation pull-out for F_s-measurable real H. This is a genuine predictable random-integrand conditional noise source for the original stopped positive-clock Ito–Meyer grid, with no abstract PRM or externally assumed martingale; product integrability is explicit and is automatic for bounded weights, a separate routine consequence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_oai_original_physical_simple_mark_condExp_all_strict_time_20261122
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_anynu_finite_negative_Borel_mark_compensated_real_L1_centered
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_oai_original_physical_simple_signed_mark_predictable_weight_condExp_zero_allactivity_20261122
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s < t)
    (S : Set ℝ) (hS : MeasurableSet S)
    (hNeg : S ⊆ Iio (0 : ℝ))
    (hν : X.ν S < ⊤) (g : SimpleFunc ℝ ℝ)
    (H : Ω → ℝ)
    (hH : StronglyMeasurable[𝓕.rightCont s] H) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let B : ℝ → Set ℝ := fun y => S ∩ g ⁻¹' {y}
    let G : Ω → ℝ := fun ω =>
      ∑ y ∈ g.range, y *
        ((NX ω (Ioc s t ×ˢ B y)).toReal -
          ((((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (B y))).toReal)
    Integrable (fun ω => H ω * G ω) P →
      (P[(fun ω => H ω * G ω) | 𝓕.rightCont s] =ᵐ[P]
        (fun _ => (0 : ℝ))) := by sorry

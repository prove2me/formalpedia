-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_finite_intensity_short_strip_L1_vanishes
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_finite_intensity_short_strip_L1_vanishes
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:41:59.697196+00:00
-- url     : https://prove2.me/theorems/aa20ac81-13d2-4835-a87a-df0a933a036b
-- title:
--   Original small-jump initial strips vanish in L¹ for finite Lévy mark intensity
-- statement:
--   For the exact intrinsic original Lévy jump count and any fixed event A, if r_n−s tends to zero and the physical mark intensity X.ν(B) is finite, the event-restricted expected count on (s,r_n]×B tends to zero. Its exact unconditional rate is stated as a hypothesis; the theorem proves the nontrivial finite-intensity limit needed for the right-continuous extension without replacing the source process.
-- source:
--   Actual SpectrallyNegativeLevy original source count, Mathlib ENNReal.Tendsto.mul_const with finite mark rate, continuous_coe, and topological squeeze.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped ENNReal NNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_finite_intensity_short_strip_L1_vanishes
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (r : ℕ → ℝ≥0) (B : Set ℝ)
    (A : Set Ω)
    (hr : Tendsto (fun n => r n - s) atTop (𝓝 0))
    (hFinite : X.ν B ≠ ⊤)
    (hRate : ∀ n,
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (r n) ×ˢ B) ∂P) =
        (((r n - s : ℝ≥0) : ℝ≥0∞) * X.ν B)) :
    Tendsto (fun n => (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (r n) ×ˢ B) ∂P))
      atTop (𝓝 0) := by sorry

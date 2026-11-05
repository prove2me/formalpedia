-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_public_mark_kernel_tonelli
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_original_public_mark_kernel_tonelli
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:49:21.531469+00:00
-- url     : https://prove2.me/theorems/4792d564-59f0-498e-b7f9-2b0ad851478d
-- title:
--   Public original Lévy intrinsic marked-count mean-measure Tonelli representation
-- statement:
--   Use the public Proved σ-finite original jump-count kernel on the exact original sample space to construct the original mean marked-counting measure as P.bind κ. Identify its values on all measurable time-mark sets and prove the exact nonnegative-test Tonelli identity by the pinned Mathlib Measure.bind_apply and Measure.lintegral_bind. This is a public P2-A alternative to a private P2-D Tonelli theorem, with no compensator or independent model.

import Mathlib.MeasureTheory.Measure.GiryMonad
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_actual_source_intrinsic_sfinite_kernel
open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_original_public_mark_kernel_tonelli
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (g : (ℝ≥0 × ℝ) → ℝ≥0∞) (hg : Measurable g) :
    ∃ M : Measure (ℝ≥0 × ℝ),
      (∀ C : Set (ℝ≥0 × ℝ), MeasurableSet C →
        M C = (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) C ∂P)) ∧
      (∫⁻ p, g p ∂M) =
        (∫⁻ ω, ∫⁻ p, g p ∂
          ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u, X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) ∂P) := by sorry

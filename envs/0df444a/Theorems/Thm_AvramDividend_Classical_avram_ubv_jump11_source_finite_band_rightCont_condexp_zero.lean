-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_jump11_source_finite_band_rightCont_condexp_zero
-- name    : AvramDividend.Classical.avram_ubv_jump11_source_finite_band_rightCont_condexp_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T09:53:03.525178+00:00
-- url     : https://prove2.me/theorems/b821b059-6ca6-41b6-b670-5463f1442cbb
-- title:
--   Original finite-band marked source count is centred at the right-continuous past
-- statement:
--   For the original spectrally negative Levy process, the finite-intensity intrinsic negative-jump count over a future marked interval, compensated by time times the Levy mass, has conditional expectation zero at the right-continuous past. The result derives all raw-past factorisation and unconditional rate premises from the source laws, requiring only marked count measurability, finite Levy band, and explicit initial-clock approximation.
-- source:
--   Source-exact conditional centring from 859bf7be, 9db23f4e, c34e4241; useful for true-process jump finite-grid conditional martingale and a44d4219.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_borel_marked_unconditional_levy_rate
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_rectangle_of_unconditional_rate
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_P2_raw_implies_rightCont_finite_band_centering
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_jump11_source_finite_band_rightCont_condexp_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (r : ℕ → ℝ≥0)
    (hsr : ∀ n, s < r n) (hrt : ∀ n, r n ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (J : ℝ≥0 → ℝ≥0 → Ω → ℝ≥0∞)
    (hJsource : ∀ a b ω, J a b ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
       (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
       (Ioc a b ×ˢ B))
    (hShort : Tendsto (fun n => r n - s) atTop (𝓝 0))
    (hLong : Tendsto (fun n => t - r n) atTop (𝓝 (t - s)))
    (hFinite : X.ν B ≠ ⊤) (hJmeas : Measurable (J s t)) :
    P[(fun ω => (J s t ω).toReal -
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) |
      𝓕.rightCont s] =ᵐ[P] 0 := by sorry

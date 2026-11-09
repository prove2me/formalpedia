-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_jump11_original_finite_band_bounded_predictable_condexp_zero
-- name    : AvramDividend.Classical.avram_ubv_jump11_original_finite_band_bounded_predictable_condexp_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T11:19:39.171188+00:00
-- url     : https://prove2.me/theorems/dea95c8c-3888-4125-9056-236d82cc8c08
-- title:
--   Original finite Lévy-band compensated count remains centred under bounded predictable weights
-- statement:
--   For the literal same-process marked negative-jump count on a finite-intensity Borel band, derive conditional mean zero of every bounded right-continuous past measurable predictable scalar weight times the compensated future count. Inputs only use the process source, finite band, and explicit right-continuity approximants. Source rate and integrability and conditional centring are obtained from existing Proved original theorems; this interface feeds the finite-grid predictable jump martingale in the original σ=0 stopped source.
-- source:
--   UBV-JUMP11 source-exact six-Proved-lemma integration: 859bf7be,52b7e6d6,5cb1e247,b821b059,c587c43a,4127b09d.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_borel_marked_unconditional_levy_rate
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_finite_nu_count_real_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_intrinsic_marked_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump11_source_finite_band_rightCont_condexp_zero
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_bounded_predictable_weight_count_condExp_zero
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_jump11_original_finite_band_bounded_predictable_condexp_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) (r : ℕ → ℝ≥0)
    (hsr : ∀ n, s < r n) (hrt : ∀ n, r n ≤ t)
    (hShort : Tendsto (fun n => r n - s) atTop (𝓝 0))
    (hLong : Tendsto (fun n => t - r n) atTop (𝓝 (t - s)))
    (B : Set ℝ) (hB : MeasurableSet B) (hFinite : X.ν B < ⊤)
    (J : Ω → ℝ≥0∞)
    (hJsource : ∀ ω, J ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
       (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
       (Ioc s t ×ˢ B))
    (H : Ω → ℝ) (C : ℝ)
    (hH : StronglyMeasurable[𝓕.rightCont s] H)
    (hBound : ∀ᵐ ω ∂P, ‖H ω‖ ≤ C) :
    P[(fun ω => H ω * ((J ω).toReal -
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal)) |
      𝓕.rightCont s] =ᵐ[P] 0 := by sorry

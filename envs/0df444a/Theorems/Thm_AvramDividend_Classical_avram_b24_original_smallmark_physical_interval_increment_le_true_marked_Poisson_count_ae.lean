-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_original_smallmark_physical_interval_increment_le_true_marked_Poisson_count_ae
-- name    : AvramDividend.Classical.avram_b24_original_smallmark_physical_interval_increment_le_true_marked_Poisson_count_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:39:13.616638+00:00
-- url     : https://prove2.me/theorems/c18e3c2d-d171-419f-9003-cea5dd290ba6
-- title:
--   Original finite-activity compensated smallmark increments bounded by actual marked Poisson count on every physical interval
-- statement:
--   On the actual original spectrally negative finite-activity Lévy source Ω/P, EVERY intrinsic compensated smallmark source witness Jsmall satisfying only its a.e. all-time cutoff residual limit obeys, simultaneously on a single P-conull event and for all physical s≤t≤T, an exact absolute variation bound: the ACTUAL negative-small marked Poisson counting measure of Ioc s t × Ioo(-1,0) plus (t-s) times the complete smallmark compensator first-moment norm. This refines the B24 finite marked support count estimate into a physical measurable marked source bound compatible with original Campbell intensity/expectation and true stopping clocks. No large negative mark moments, no auxiliary process and no postruin extension.
-- source:
--   Proved actual finite smallmark jump-step path increment/card theorem, a20 original marked Poisson count equals finite physical support cardinal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_original_smallmark_physical_interval_increment_le_true_marked_Poisson_count_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hJsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω)
        atTop (𝓝 (Jsmall t ω)))
    (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ (s t : ℝ≥0), s ≤ t → t ≤ T →
      ‖Jsmall t ω - Jsmall s ω‖ ≤
      (((Measure.count.restrict {u : ℝ≥0 |
         0 < u ∧ X.X u ω -
           Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
         (fun u : ℝ≥0 => (u, X.X u ω -
           Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
         (Ioc s t ×ˢ Ioo (-1 : ℝ) 0)).toReal +
      ((t : ℝ) - (s : ℝ)) *
        ‖∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν‖ := by sorry

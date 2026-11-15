-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_original_finiteactivity_smallmark_increment_true_interval_count_variation_ae
-- name    : AvramDividend.Classical.avram_b24_original_finiteactivity_smallmark_increment_true_interval_count_variation_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:37:09.965334+00:00
-- url     : https://prove2.me/theorems/7aad2bfc-44b3-4044-8f92-97556a35fa12
-- title:
--   Any original finite-activity compensated smallmark path has exact physical interval variation controlled by true negative marks and compensator drift
-- statement:
--   For the actual finite-negative-activity spectrally negative Lévy source X on its original sample space, and every arbitrary intrinsic compensated smallmark limit witness Jsmall satisfying the B24 all-time a.e. residual limit, on one common P-conull event and every bounded physical horizon T there is a SINGLE finite support S of true original X jump times such that ALL physical increments s≤t≤T satisfy an exact pathwise absolute variation bound: actual number of original small-negative jump times in (s,t] plus elapsed time (t-s) times the complete finite signed ν smallmark compensator norm. The original strict-left/inclusive-right jump convention is retained at terminal ruin; no postruin continuation or large negative mark moments. This supplies a source finite variation and integrable per-cell interval envelope for original stopped physical Itô-Meyer mark meshes.
-- source:
--   Original B24 fixed-horizon intrinsic Jsmall genuine marked-step path representation and true negative-mark finite step increment/card theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_original_finiteactivity_smallmark_increment_true_interval_count_variation_ae
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
    ∀ᵐ ω ∂P, ∃ S : Finset ℝ≥0,
      (∀ u : ℝ≥0, u ∈ S ↔ 0 < u ∧ u ≤ T ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0) ∧
      ∀ (s t : ℝ≥0), s ≤ t → t ≤ T →
        ‖Jsmall t ω - Jsmall s ω‖ ≤
        ((S.filter (fun u =>
          s < u ∧ u ≤ t ∧
          -1 < X.X u ω -
             Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∧
          X.X u ω -
             Function.leftLim (fun v : ℝ≥0 => X.X v ω) u < 0)).card : ℝ) +
        ((t : ℝ) - (s : ℝ)) *
          ‖∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν‖ := by sorry

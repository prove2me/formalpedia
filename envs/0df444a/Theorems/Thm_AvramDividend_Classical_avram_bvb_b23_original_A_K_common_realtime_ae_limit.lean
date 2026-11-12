-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_b23_original_A_K_common_realtime_ae_limit
-- name    : AvramDividend.Classical.avram_bvb_b23_original_A_K_common_realtime_ae_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T00:20:32.604306+00:00
-- url     : https://prove2.me/theorems/5c3bcf75-baac-49b4-8fd3-e40b4919f544
-- title:
--   Original masked loss upper bound on the genuine uniform floor grid
-- statement:
--   The actual original prepayment reserve's discounted open-cap negative mark loss on the refining uniform floor grid is eventually no greater than its closed-cap contact-time loss plus arbitrary epsilon, even when the grid misses contact occupation.
-- source:
--   Root-connected one-sided a.e. floor-sampling input for phys95/efbae9c3.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b23_original_A_K_common_nat_pointwise_limit
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b23_original_real_horizon_away_ruin_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb_b23_original_A_K_common_realtime_ae_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ) (C : ℝ≥0∞)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω)
    (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (q T : ℝ) (hT : 0 < T)
    (hsource : ∀ r : ℝ≥0, (r : ℝ) ≤ T →
       X.X r ω = (r : ℝ) * X.drift) :
    let S : ℝ≥0 := ⟨T, hT.le⟩
    let τ : ℝ≥0∞ := ruinTime X x D ω
    let U : ℝ≥0 → ℝ := fun s => Function.leftLim
      (fun z : ℝ≥0 => x + X.X z ω - rightLimit D z ω) s
    let s : ℕ → ℝ → ℝ≥0 := fun n r => Real.toNNReal
      (T * (⌊((((Real.toNNReal r : ℝ≥0) : ℝ) / T) *
        ((n : ℝ) + 2))⌋₊ : ℝ) / ((n : ℝ) + 2))
    let F : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ))) *
      ∫ z in Iio (0 : ℝ), w (U t + z) - w (U t) ∂X.ν
    let f : ℝ → ℝ := fun r =>
      if ((Real.toNNReal r : ℝ≥0) : ℝ≥0∞) < τ ∧
         0 ≤ U (Real.toNNReal r) ∧
         ENNReal.ofReal (U (Real.toNNReal r)) ≤ C
      then F (Real.toNNReal r) else 0
    ∀ᵐ r ∂((volume : Measure ℝ).restrict (Icc 0 T)),
      (Tendsto (fun n : ℕ =>
        if (s n r : ℝ≥0∞) < τ ∧
          0 ≤ U (s n r) ∧ ENNReal.ofReal (U (s n r)) ≤ C
        then F (s n r) else 0) atTop (𝓝 (f r))) ∧
      (Tendsto (fun n : ℕ =>
        if 0 < Real.toNNReal r ∧
          ((Real.toNNReal r : ℝ≥0) : ℝ) < T - T / ((n : ℝ) + 2) ∧
          ((Real.toNNReal r : ℝ≥0) : ℝ≥0∞) ≤ τ ∧
          0 ≤ U (Real.toNNReal r) ∧
          ENNReal.ofReal (U (Real.toNNReal r)) ≤ C
        then F (Real.toNNReal r) else 0) atTop (𝓝 (f r))) := by sorry

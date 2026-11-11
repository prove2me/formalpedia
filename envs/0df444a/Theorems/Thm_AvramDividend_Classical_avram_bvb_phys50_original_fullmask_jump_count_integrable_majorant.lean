-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys50_original_fullmask_jump_count_integrable_majorant
-- name    : AvramDividend.Classical.avram_bvb_phys50_original_fullmask_jump_count_integrable_majorant
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T14:38:33.308244+00:00
-- url     : https://prove2.me/theorems/9a6793e4-e9c4-4181-9eda-de31e50a0e72
-- title:
--   Original stopped finite-activity discounted jump reward dominated by integrable physical count
-- statement:
--   The original negative-jump count over the fixed physical horizon is integrable; a deterministic finite constant bounds each original stopped full-mask discounted marked reward integral almost everywhere by that count. Finite negative activity and compact finite cap ensure the bound, with no change of probability space.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb_phys50_original_fullmask_jump_count_integrable_majorant
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 < T)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let U : ℝ≥0 → Ω → ℝ := fun t ω => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    let H : ℕ → (ℝ≥0 × Ω) × ℝ → ℝ := fun n p =>
      if 0 < p.1.1 ∧ (p.1.1 : ℝ) < T - δ n ∧
         (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 ∧
         0 ≤ U p.1.1 p.1.2 ∧ ENNReal.ofReal (U p.1.1 p.1.2) ≤ C ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (U p.1.1 p.1.2 + p.2) - w (U p.1.1 p.1.2)) else 0
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {t : ℝ≥0 | 0 < t ∧ X.X t ω -
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t, X.X t ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)))
    let J : ℕ → Ω → ℝ := fun n ω =>
      ∫ p, H n ((p.1, ω), p.2) ∂(NX ω)
    let N : Ω → ℝ := fun ω =>
      ((NX ω) (Ioc (0 : ℝ≥0) (Real.toNNReal T) ×ˢ Iio (0 : ℝ))).toReal
    ∃ K : ℝ, 0 ≤ K ∧ Integrable N P ∧
      ∀ n : ℕ, ∀ᵐ ω ∂P, ‖J n ω‖ ≤ K * N ω := by sorry

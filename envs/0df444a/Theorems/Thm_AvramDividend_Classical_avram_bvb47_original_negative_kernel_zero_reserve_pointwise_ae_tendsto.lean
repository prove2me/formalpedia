-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb47_original_negative_kernel_zero_reserve_pointwise_ae_tendsto
-- name    : AvramDividend.Classical.avram_bvb47_original_negative_kernel_zero_reserve_pointwise_ae_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:43:47.960399+00:00
-- url     : https://prove2.me/theorems/45cda3b2-1245-4585-90ab-8ce77f9686be
-- title:
--   Original finite-activity negative-mark kernel almost everywhere pointwise limit at reserve zero
-- statement:
--   For original w continuous from right at 0 and identically zero for negative reserves, y_n=C/(n+2) tends to zero and, for each z<0, y_n+z<0 eventually. Thus original kernel w(y_n+z)-w(y_n) converges to w(z)-w0 for ν-almost-every negative mark z. This is the exact pointwise half of dominated convergence without modification of original ν.
-- source:
--   Original finite-activity negative ν, continuity of candidate w, original bvb45 kernel limit; Mathlib dominated convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb47_original_negative_kernel_zero_reserve_pointwise_ae_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hFinite : C ≠ ⊤)
    (hwCont : ContinuousOn w (Ici (0 : ℝ)))
    (hwNeg : ∀ y : ℝ, y < 0 → w y = 0) :
    ∀ᵐ z ∂(X.ν.restrict (Iio (0 : ℝ))),
      Tendsto
        (fun n : ℕ => w (C.toReal / ((n : ℝ) + 2) + z) -
          w (C.toReal / ((n : ℝ) + 2)))
        atTop (𝓝 (w ((0 : ℝ) + z) - w 0)) := by sorry

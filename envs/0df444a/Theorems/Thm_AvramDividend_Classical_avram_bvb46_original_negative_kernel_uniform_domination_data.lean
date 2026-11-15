-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb46_original_negative_kernel_uniform_domination_data
-- name    : AvramDividend.Classical.avram_bvb46_original_negative_kernel_uniform_domination_data
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:43:46.314584+00:00
-- url     : https://prove2.me/theorems/dffd0557-7ced-4af1-850d-bf37d6b3d95a
-- title:
--   Original finite-activity negative-mark kernel uniform integrable envelope and measurable slices
-- statement:
--   For original ν finite on negative marks, original w continuous on [0,∞) and zero on negative reserve, and C finite positive, find an integrable g dominating absolute original kernel w(y_n+z)-w(y_n) for all n, with exact AEStronglyMeasurable slices. Use compact [0,C] bound M on w, global zero-below extension, constant 2M integrable against finite ν. This is the dominated-convergence envelope for the actual kernel and weak zero HJB.
-- source:
--   Original finite-activity negative ν, continuity of candidate w, original bvb45 kernel limit; Mathlib dominated convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb46_original_negative_kernel_uniform_domination_data
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hFinite : C ≠ ⊤)
    (hwCont : ContinuousOn w (Ici (0 : ℝ)))
    (hwNeg : ∀ y : ℝ, y < 0 → w y = 0) :
    ∃ g : ℝ → ℝ,
      Integrable g (X.ν.restrict (Iio (0 : ℝ))) ∧
      (∀ n : ℕ, AEStronglyMeasurable
        (fun z : ℝ => w (C.toReal / ((n : ℝ) + 2) + z) -
          w (C.toReal / ((n : ℝ) + 2)))
        (X.ν.restrict (Iio (0 : ℝ)))) ∧
      (∀ n : ℕ, ∀ᵐ z ∂(X.ν.restrict (Iio (0 : ℝ))),
        ‖w (C.toReal / ((n : ℝ) + 2) + z) -
          w (C.toReal / ((n : ℝ) + 2))‖ ≤ g z) := by sorry

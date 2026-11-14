-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_capHJB50_original_BV_full_cap_generator_sign_of_local_lipschitz
-- name    : AvramDividend.Classical.avram_bva_capHJB50_original_BV_full_cap_generator_sign_of_local_lipschitz
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T17:17:17.643214+00:00
-- url     : https://prove2.me/theorems/cbf5ee20-2709-47d1-8781-ddf162e59377
-- title:
--   Original standing BV full finite-cap HJB sign from local C1 Lipschitz with automatic candidate bound
-- statement:
--   For the actual original Standing spectrally negative bounded variation process, any finite dividend cap with original candidate continuous/nonnegative on nonnegative reserves, zero on negatives, C1 interior, generator and gradient verification, plus Lipschitz control on a fixed positive reserve floor to full closed cap, yields the genuine upper-cap generator inequality retaining all negative Lévy marks and continuous dividends. Original candidate is automatically bounded by w(cap) on the entire closed cap, removing an artificial global boundedness assumption. No false A22 strict interior spatial mask.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_capHJB50_original_BV_full_cap_generator_sign_of_local_lipschitz
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (hwCont : ContinuousOn w (Ici (0 : ℝ)))
    (hw0 : 0 ≤ w 0)
    (hwNeg : ∀ y : ℝ, y < 0 → w y = 0)
    (hwSmooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwGen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hwGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (ε L K : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 2)
    (hεc : ε ≤ C.toReal)
    (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hKL : L ≤ K) (hKM : 2 * w C.toReal ≤ K * (ε / 2))
    (hLip : ∀ a ∈ Icc (ε / 2) C.toReal,
      ∀ b ∈ Icc (ε / 2) C.toReal,
      |w a - w b| ≤ L * |a - b|)
    (y : ℕ → ℝ)
    (hy : Tendsto y atTop (𝓝 C.toReal))
    (hyInside : ∀ n, 0 < y n ∧ ENNReal.ofReal (y n) < C)
    (hyBand : ∀ n, y n ∈ Icc ε C.toReal)
    (hMeas : ∀ n, AEStronglyMeasurable
      (fun z : ℝ => w (y n + z) - w (y n))
      (X.ν.restrict (Iio (0 : ℝ)))) :
    X.drift + (∫ z in Iio (0 : ℝ),
      w (C.toReal + z) - w C.toReal ∂X.ν)
      - q * w C.toReal ≤ 0 := by sorry

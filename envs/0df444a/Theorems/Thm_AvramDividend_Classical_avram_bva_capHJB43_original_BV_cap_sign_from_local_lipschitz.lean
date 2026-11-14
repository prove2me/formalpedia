-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_capHJB43_original_BV_cap_sign_from_local_lipschitz
-- name    : AvramDividend.Classical.avram_bva_capHJB43_original_BV_cap_sign_from_local_lipschitz
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T17:17:25.501619+00:00
-- url     : https://prove2.me/theorems/d49cf246-dbeb-4b80-bcc3-9475f1dfaf41
-- title:
--   Original infinite BV finite-cap HJB sign from local source candidate Lipschitz and original Lévy measure
-- statement:
--   Given original Standing bounded-variation spectrally negative Levy process, original candidate continuous on nonnegative reserves and zero below, interior generator and slope inequalities, a local Lipschitz witness between a positive reserve floor and finite cap and a candidate bound on the closed cap, derive the TRUE closed upper-cap HJB drift plus full unmasked compensated negative mark rate nonpositive. The original negative Levy measure supplies integrability of small/large claim envelope; original atomlessness handles nonzero w(0). Remaining independent source work is near-cap derivative bootstrap for L and stopped true dividend cash Stieltjes formula.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_capHJB43_original_BV_cap_sign_from_local_lipschitz
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (hwCont : ContinuousOn w (Ici (0 : ℝ)))
    (hwNeg : ∀ y : ℝ, y < 0 → w y = 0)
    (hwGen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hwGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (ε L M K : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 2)
    (hεc : ε ≤ C.toReal)
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hKL : L ≤ K) (hKM : 2 * M ≤ K * (ε / 2))
    (hBound : ∀ r ∈ Icc (0 : ℝ) C.toReal, |w r| ≤ M)
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

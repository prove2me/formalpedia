-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger23_original_samegrid_prepost_gradient_jump_bound
-- name    : AvramDividend.Classical.avram_gledger23_original_samegrid_prepost_gradient_jump_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T13:23:06.801699+00:00
-- url     : https://prove2.me/theorems/0f1b9fe6-581c-4fb5-b6cb-6ee76fa3ede6
-- title:
--   Original Gaussian prepayment versus postpayment gradient jump bound
-- statement:
--   For the identical original Levy process and actual dividend control, if both the prepayment reserve and the postpayment reserve at one grid time remain in one compact interior C2 band with a bounded second derivative, their Gaussian Taylor gradient coefficients differ by no more than the derivative Lipschitz constant times the original nonnegative right dividend jump. This is the exact missing coefficient alignment between the Proved four-event chronological grid ledger ed0d8024 and the Proved centred original source grid ad7f605e. It makes no claim of summed L2 convergence or independent Brownian representation; that still requires the authentic bounded-prefix dividend variation and predictable isometry estimates.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ubv_C2_interior_band_gradient_lipschitz
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger23_original_samegrid_prepost_gradient_jump_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (K : ℝ≥0)
    (hK : ∀ y ∈ Icc a b, ‖deriv (deriv w) y‖₊ ≤ K)
    (s : ℝ≥0) (ω : Ω)
    (hPre : riskProcess X x D s ω ∈ Icc a b)
    (hPost : x + X.X s ω - rightLimit D s ω ∈ Icc a b)
    (hRight : 0 ≤ rightLimit D s ω - D s ω) :
    |deriv w (riskProcess X x D s ω) -
      deriv w (x + X.X s ω - rightLimit D s ω)| ≤
        (K : ℝ) * (rightLimit D s ω - D s ω) := by sorry

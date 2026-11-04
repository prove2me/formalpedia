-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_ubv_C2_stopped_atoms_interior_band_summable
-- name    : AvramDividend.Classical.avram_p4_d_dividend_ubv_C2_stopped_atoms_interior_band_summable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:31:42.632211+00:00
-- url     : https://prove2.me/theorems/f0479a0e-2ed0-4b10-a06c-9e495848ce4b
-- title:
--   Same-original UBV C2 interior stopped band makes every discounted right-payment correction absolutely summable and nonpositive
-- statement:
--   For the actual source X and left-continuous right-payment D, a fully justified compact band inside 0<U<C contains both post-source/pre-D and post-D values at all indexed payment atoms. The original C2 interior regularity plus a derivative envelope yields the precise secant bound on these two actual states. Their difference is exactly the nonnegative right payment atom, including simultaneous source jumps. If the discounted original payment atoms sum finitely, the original signed right-dividend corrections converge absolutely and have nonpositive sum. This explicitly excludes boundary-crossing payments unless handled by a separate cap/zero extension, and makes no stochastic Ito identity claim.
-- source:
--   Avram–Palmowski–Pistorius Prop. 4(i), Eq. 5.13; source pinned UBV compact-band P4-D helper c4293baa and source countable local-secant summability P4-D e4e52ea2.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_ubv_C2_interior_band_secant_lipschitz
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_countable_rightjump_local_secant_summable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_ubv_C2_stopped_atoms_interior_band_summable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (C : ℝ≥0∞)
    (hwC2 : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (K : ℝ≥0) (hK : ∀ y ∈ Icc a b, ‖deriv w y‖₊ ≤ K)
    {ι : Type*} (t : ι → ℝ≥0) (ω : Ω)
    (hPre : ∀ i : ι, t i = 0 ∨ (t i : ℝ≥0∞) < ruinTime X x D ω)
    (hStates : ∀ i : ι,
      riskProcess X x D (t i) ω ∈ Icc a b ∧
      x + X.X (t i) ω - rightLimit D (t i) ω ∈ Icc a b)
    (hPayNonneg : ∀ i : ι, 0 ≤ rightLimit D (t i) ω - D (t i) ω)
    (hPaySummable : Summable (fun i : ι =>
      Real.exp (-(q * (t i : ℝ))) *
        (rightLimit D (t i) ω - D (t i) ω))) :
    Summable (fun i : ι =>
      Real.exp (-(q * (t i : ℝ))) *
        ((rightLimit D (t i) ω - D (t i) ω) +
          w (x + X.X (t i) ω - rightLimit D (t i) ω) -
          w (riskProcess X x D (t i) ω))) ∧
    (∑' i : ι, Real.exp (-(q * (t i : ℝ))) *
      ((rightLimit D (t i) ω - D (t i) ω) +
        w (x + X.X (t i) ω - rightLimit D (t i) ω) -
        w (riskProcess X x D (t i) ω))) ≤ 0 := by sorry

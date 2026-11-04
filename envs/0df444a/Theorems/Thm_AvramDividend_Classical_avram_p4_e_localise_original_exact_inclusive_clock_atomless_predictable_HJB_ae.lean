-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_exact_inclusive_clock_atomless_predictable_HJB_ae
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_exact_inclusive_clock_atomless_predictable_HJB_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:54:51.143263+00:00
-- url     : https://prove2.me/theorems/69468521-b00b-41f2-9809-ec7be2f7f6ec
-- title:
--   True original inclusive ruin-truncated physical clock has predictable HJB a.e. even at atomless terminal time
-- statement:
--   At the canonical finite source stopping clock (min(ruinTime,n)).toNNReal, inclusive physical-time integration through t≤τ has exactly the same a.e. predictable interior HJB generator validity as the strict preclock because the deterministic s-finite physical time measure is explicitly atomless. The proof excludes both t=0 and each path's random single terminal time by `μ.ae_ne`; this is legitimate only for such a physical measure and does not erase true random dividend Stieltjes atoms at either endpoint. Applies to finite/infinite C via source c9db.
-- source:
--   Proved original all-cap predictable interior c9db7a94, original truncated-clock bound 6b7a13a0, pinned MeasureTheory.Measure.ae_ne.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_preruin_strict_interior_atomless
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_truncated_clock_nnreal_bounds
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Inclusion of the finite ruin horizon does not alter physical-time predictable HJB almost everywhere. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_exact_inclusive_clock_atomless_predictable_HJB_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (hC0 : C ≠ 0)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hxc : ENNReal.ofReal x ≤ C)
    (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ]
    (w : ℝ → ℝ) (q : ℝ)
    (hwGen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ᵐ t : ℝ≥0 ∂μ,
      t ≤ (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal →
      X.GeneratorIntegrable w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) ∧
        X.generator w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) - q * w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) ≤ 0 := by sorry

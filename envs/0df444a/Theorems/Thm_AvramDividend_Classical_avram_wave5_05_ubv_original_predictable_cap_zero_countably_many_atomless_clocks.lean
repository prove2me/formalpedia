-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_cap_zero_countably_many_atomless_clocks
-- name    : AvramDividend.Classical.avram_wave5_05_ubv_original_predictable_cap_zero_countably_many_atomless_clocks
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T11:38:39.08355+00:00
-- url     : https://prove2.me/theorems/a89a4d08-4c2f-400d-9c43-46e709218b75
-- title:
--   Simultaneous almost-sure null predictable cap-contact mass for countably many original-process atomless generator clocks and arbitrary characteristic weights
-- statement:
--   In the same original Lévy source X and actual capped dividend D, the predictable leftLimit of x+X−rightLimit D may contact the cap on a random thin set but has zero positive surviving mass under every prescribed atomless s-finite clock μ_n, for every n in a countable family, simultaneously on one P-probability-one event. We allow arbitrary nonnegative extended weights indexed by n, even infinite at cap. This is the countable-localisation bridge needed to combine Gaussian dt characteristic, jump dt times Lévy measure, and generator estimates across cutoffs while allowing x=c and dividends at cap. It does not eliminate random dividend Stieltjes mass or semimartingale cap local time.
-- source:
--   Original same-process predictable cap-nullity already Proved f8199679-8516-46fa-b24a-b17cf33e8b8b; original process UBV admissibility; mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43; corrected core 429e17ca-5528-40b5-b593-7c03973d0706 unchanged.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_cap_contact_weighted_atomless_zero

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave5_05_ubv_original_predictable_cap_zero_countably_many_atomless_clocks
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (hCap : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω → riskProcess X x D s ω ≤ c)
    (μ : ℕ → Measure ℝ≥0)
    (hsf : ∀ n, SFinite (μ n))
    (hatom : ∀ n, NullSingletonClass (μ n))
    (weight : ℕ → ℝ≥0 → Ω → ℝ≥0∞) :
    ∀ᵐ ω ∂P, ∀ n : ℕ,
      (∫⁻ t : ℝ≥0,
        if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω ∧
            Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t = c
        then weight n t ω else 0 ∂μ n) = 0 := by sorry

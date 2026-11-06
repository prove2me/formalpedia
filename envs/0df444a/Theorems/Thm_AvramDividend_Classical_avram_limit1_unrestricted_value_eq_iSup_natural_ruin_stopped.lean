-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit1_unrestricted_value_eq_iSup_natural_ruin_stopped
-- name    : AvramDividend.Classical.avram_limit1_unrestricted_value_eq_iSup_natural_ruin_stopped
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T23:33:10.256594+00:00
-- url     : https://prove2.me/theorems/b748273d-98cf-4dba-88be-d9361c9e6d49
-- title:
--   Unrestricted dividend optimum equals supremum over original natural stopped Stieltjes rewards
-- statement:
--   For the actual original Lévy process and all original admissible dividend strategies, the unrestricted value function is precisely the supremum of expected discounted ruin-stopped Stieltjes payments over every strategy, admissibility witness and natural horizon. This is an exact stronger interface to the unrestricted C=top branch of Avram local verification. It uses only the already Proved original per-strategy dividendValue natural-stopped supremum equality (5cd004b0), requires no additional measurability or integrability assumption, and preserves the time-zero atom and strict payment endpoint.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_10_original_dividendValue_eq_iSup_natural_ruin_stopped

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit1_unrestricted_value_eq_iSup_natural_ruin_stopped
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ) :
    valueFunction X q x =
      ⨆ D : ℝ≥0 → Ω → ℝ, ⨆ hD : IsAdmissible X x D, ⨆ n : ℕ,
        (∫⁻ ω, ∫⁻ t in
          paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω) ∂P) := by sorry

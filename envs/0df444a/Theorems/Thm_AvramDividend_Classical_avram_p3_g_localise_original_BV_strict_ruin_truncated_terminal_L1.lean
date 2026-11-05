-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_BV_strict_ruin_truncated_terminal_L1
-- name    : AvramDividend.Classical.avram_p3_g_localise_original_BV_strict_ruin_truncated_terminal_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:09:27.903989+00:00
-- url     : https://prove2.me/theorems/d6bdcbd6-4b4f-4fb1-a64a-e1dc17c9ff0e
-- title:
--   Genuine original BV strict terminal integrability under the finite ruin clock
-- statement:
--   Under the actual original spectrally negative bounded-variation Levy source, admissible dividend strategy, normalisation and finite P, the discounted original riskProcess payoff at deterministic S<T, masked by the true truncated ruin clock min(ruinTime,T).toNNReal, is P-integrable. This inherits the already Proved strict preterminal L1 theorem and uses an exact strict clock event equivalence. No boundary occupation or surrogate process is assumed.
-- source:
--   Proved physical strict preterminal L1 d086b85a and Proved P3-G strict/inclusive original ruin-clock endpoint equality b4677f24.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_preterminal_L1
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_ruin_clock_exact_strict_inclusive_endpoints

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_g_localise_original_BV_strict_ruin_truncated_terminal_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hXzero : ∀ ω, X.X 0 ω = 0) (hfinite : IsFiniteMeasure P)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (T S : ℝ≥0) (hST : S < T) :
    Integrable (fun ω =>
      if (S : ℝ≥0∞) <
          (((min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal) : ℝ≥0∞)
      then Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω)
      else 0) P := by sorry

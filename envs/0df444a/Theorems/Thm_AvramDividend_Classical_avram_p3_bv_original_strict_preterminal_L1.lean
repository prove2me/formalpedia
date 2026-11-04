-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_preterminal_L1
-- name    : AvramDividend.Classical.avram_p3_bv_original_strict_preterminal_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:35:48.143212+00:00
-- url     : https://prove2.me/theorems/d086b85a-4438-46a3-b237-9af6fcbc8b5d
-- title:
--   Actual BV surviving pre-right-dividend terminal is integrable from physical drift strip
-- statement:
--   For the true original BV source, source-normalised at X_0=0, any genuine adapted nondecreasing dividend strategy and a continuous-on-[0,infinity) candidate vanishing at negative reserves, the discounted candidate evaluated at the before-rightpayment reserve at a deterministic strictly surviving clock is integrable on the original finite probability measure. The physical drift upper bound, strictly pre-ruin nonnegativity, measurability and compact continuity are all discharged by separately Proved source helpers. This establishes only terminal L1, not stochastic HJB compensation.
-- source:
--   Original BV survival drift strip, measurable controlled reserve and ruin time, Borel candidate, and compact-strip L1 closure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_preruin_preterminal_drift_strip
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_preterminal_integrable_of_strip
import Theorems.Thm_AvramDividend_Classical_riskProcess_measurable
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_local_verification_candidate_borel_and_postPayment_adapted
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_original_strict_preterminal_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hXzero : ∀ ω, X.X 0 ω = 0) (hfinite : IsFiniteMeasure P)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (S : ℝ≥0) :
    Integrable (fun ω => if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω)
      else 0) P := by sorry

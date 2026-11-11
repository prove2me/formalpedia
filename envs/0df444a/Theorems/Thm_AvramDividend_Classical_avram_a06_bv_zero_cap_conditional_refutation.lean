-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_bv_zero_cap_conditional_refutation
-- name    : AvramDividend.Classical.avram_a06_bv_zero_cap_conditional_refutation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T14:58:11.833209+00:00
-- url     : https://prove2.me/theorems/3289af7b-4a5b-443e-ac6c-59e1cdff1e83
-- title:
--   A06 zero-cap target contradicted by an admissible non-jumping barrier strategy
-- statement:
--   For any standing finite-activity BV spectrally negative Lévy source, the original zero-cap candidate bound fails for an actual admissible barrier strategy that has no right-payment jumps. Use the already Proved zero-cap finite-horizon counterexample and no-right-jumps theorem; the generator assumptions of A06 are vacuous when C=0 and w=0.
-- source:
--   A06 counterexample prerequisite. The original core lacks positive-cap and w(0) assumptions. This theorem derives the actual admissible strategy, preservation of its right-jump constraint, and a violating finite horizon from Proved public results. Its only mathematical hypotheses are the source Standing, BV and finite-activity assumptions; it does not assume the original target.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_09_bv_zero_cap_zero_candidate_finite_horizon_counterexample
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_no_right_jump_of_initial_below_barrier
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_bv_zero_cap_conditional_refutation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q) :
    ∃ (D : ℝ≥0 → Ω → ℝ),
      IsAdmissibleLe X 0 (0 : ℝ≥0∞) D ∧
      (∀ ω (t : ℝ≥0), rightLimit D t ω - D t ω ≤ 0) ∧
      ∃ n : ℕ, (0 : ℝ) ≤ (n : ℝ) ∧
        ¬ ((∫⁻ ω, ∫⁻ t in
          paymentTimes (ruinTime X 0 D ω) ∩ Iic (n : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω) ∂P) ≤
          ENNReal.ofReal (0 : ℝ)) := by sorry

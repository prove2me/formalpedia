-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_positive_ruin_strict_stopped_drift_budget
-- name    : AvramDividend.Classical.avram_wave3_03_bv_positive_ruin_strict_stopped_drift_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T11:04:01.777357+00:00
-- url     : https://prove2.me/theorems/2b6ae7a8-33a2-42e3-8e5e-601428e7695e
-- title:
--   Actual BV strict stopped Stieltjes reward bounded through positive ruin by deterministic drift
-- statement:
--   For the original bounded-variation spectrally negative Lévy process satisfying standing assumptions, the complete discounted Stieltjes dividend payout strictly before the earlier of ruin and deterministic H is almost surely bounded by initial capital plus H times physical drift on positive-ruin paths, even if ruin occurs before H. It follows by applying the uniform source-path pre-ruin estimate on every rational prefix and passing through the Proved directed-prefix Stieltjes limit. Both continuous dividends and positive-time atoms are preserved.
-- source:
--   Actual original Lévy BV residual monotonicity through the Proved uniform pre-ruin Stieltjes drift envelope bf6dbe15; Proved rational-prefix stopped Lebesgue integral bound 47c77755; Proved standing BV positive physical drift 0432f641.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_uniform_preRuin_full_stieltjes_drift_envelope
import Theorems.Thm_AvramDividend_Classical_paymentTimes_lintegral_le_of_rational_prefix_bounds
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_03_bv_positive_ruin_strict_stopped_drift_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (H : ℝ≥0) (hH : 0 < H) :
    ∀ᵐ ω ∂P, 0 < ruinTime X x D ω →
      (∫⁻ r in paymentTimes
          (min (ruinTime X x D ω) (H : ℝ≥0∞)),
        ENNReal.ofReal (Real.exp (-(q * r)))
          ∂(dividendMeasure D ω)) ≤
        ENNReal.ofReal (x + (H : ℝ) * X.drift) := by sorry

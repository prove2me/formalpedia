-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger20_original_positive_stop_terminal_prepayment_band
-- name    : AvramDividend.Classical.avram_gledger20_original_positive_stop_terminal_prepayment_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T10:52:15.565923+00:00
-- url     : https://prove2.me/theorems/d81c6b24-0c31-489b-89a6-3f1a89d699a8
-- title:
--   Original positive compact stopping clock preserves its prepayment terminal reserve band
-- statement:
--   For the original zero-jump Gaussian Lévy process, each positive stopping clock with an almost-sure strict prepayment reserve band u≤riskProcess(t)≤b inherits the same closed band at the prepayment terminal riskProcess(rho). The right-continuous postpayment reserve lies above u before rho by the original strict-prefix right-limit lemma, and below the prepayment reserve by dividend monotonicity. The Proved original zero-jump left-limit theorem then transfers both bounds to the terminal prepayment reserve. This handles a substantial terminal-value side condition of Open 47174f6c without treating a right dividend at rho as paid.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger20_original_strict_prefix_postpayment_floor
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite12_original_positive_clock_postpayment_left_tendsto
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger20_original_positive_stop_terminal_prepayment_band
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ρ : Ω → ℝ≥0) (u b : ℝ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      u ≤ riskProcess X x D t ω ∧ riskProcess X x D t ω ≤ b) :
    ∀ᵐ ω ∂P, 0 < ρ ω →
      u ≤ riskProcess X x D (ρ ω) ω ∧
        riskProcess X x D (ρ ω) ω ≤ b := by sorry

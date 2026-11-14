-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_genuine_stopped_negative_levy_mark_crossing_discounted_zero_boundary_cash_at_most_w0
-- name    : AvramDividend.Classical.avram_bva_a22_original_genuine_stopped_negative_levy_mark_crossing_discounted_zero_boundary_cash_at_most_w0
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T10:50:23.350439+00:00
-- url     : https://prove2.me/theorems/f75b8bb1-d297-4fd9-ae44-b8de44b2fc6e
-- title:
--   Original genuine stopped negative Lévy jump ruin-crossing discounted positive zero-boundary candidate total cash is bounded by w(0)
-- statement:
--   For the genuine original spectrally negative Levy process X, original dividend control D, initial x and any fixed path, define the exact stopped true negative Lévy mark ruin-crossing times as those positive times at or before first ruin with X_t<X_{t-} and the true controlled postpayment reserve strictly negative. For any positive discount and any nonnegative value w0 (eventually instantiated as original candidate w(0)), the complete sum of discounted w0 at all such original ruin-crossing jump times is at most w0, despite infinite source jump activity. The Proved original stopped true negative mark ruin-crossing count is at most one, so the whole discounted sum is either zero or a single e^{-qt}w0<=w0. This explicitly isolates the possible positive zero-boundary jump penalty from compensated interior mark contributions in the BVA96 C1 spatial error without falsely assuming w(0)=0, finite jump activity or an artificial spatial diagonal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_stopped_negative_levy_mark_genuine_ruin_crossing_count_at_most_one
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a22_original_genuine_stopped_negative_levy_mark_crossing_discounted_zero_boundary_cash_at_most_w0
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (q : ℝ) (hq : 0 ≤ q)
    (w0 : ℝ) (hw0 : 0 ≤ w0) :
    let R : Set ℝ≥0 := {t |
      0 < t ∧ (t : ℝ≥0∞) ≤ ruinTime X x D ω ∧
      X.X t ω < Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ∧
      riskProcess X x D t ω < 0}
    (∑' t : ℝ≥0, if t ∈ R then
      Real.exp (-(q * (t : ℝ))) * w0 else 0) ≤ w0 := by sorry

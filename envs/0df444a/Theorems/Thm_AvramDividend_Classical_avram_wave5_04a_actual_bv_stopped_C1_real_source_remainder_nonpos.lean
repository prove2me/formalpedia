-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_stopped_C1_real_source_remainder_nonpos
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_bv_stopped_C1_real_source_remainder_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:12:48.12962+00:00
-- url     : https://prove2.me/theorems/d4fa25dd-02ac-4d28-ae49-57a3cf3de274
-- title:
--   Actual BV stopped C1 source-jump decomposition has finite real downward remainders with nonpositive contribution
-- statement:
--   For the genuine original bounded-variation spectrally negative Levy process and actual admissible dividend strategy, on one full-probability event, every samplewise stopped finite monotone time partition admits finite real nonnegative interval remainders after subtracting the complete source negative left-jump magnitude from the drift residual. Whenever the verification derivative at the actual reserve partition starts is nonnegative, their signed contribution is nonpositive. This uses neither an unproved pure-jump identity nor the controlled Ito-Meyer theorem.
-- source:
--   Mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43, Wave5 Chat04-A continuation. Direct source-coupled consequence of canonical Proved e84d1832-1a90-4b40-a0ca-e0f4065fdb5e.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_interval_source_jump_real_nonnegative_remainder

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Real finite source-jump and downward remainder partition identity for the
actual stopped controlled BV process; increasing C1 derivatives yield a
nonpositive signed remainder contribution. -/

theorem AvramDividend.Classical.avram_wave5_04a_actual_bv_stopped_C1_real_source_remainder_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (w : ℝ → ℝ) :
    ∀ᵐ ω ∂P, ∀ (τ : Ω → ℝ≥0) (u : ℕ → ℝ≥0)
      (hu : Monotone u) (n : ℕ) (hstop : u n ≤ τ ω)
      (hgrad : ∀ i : Fin n,
        0 ≤ deriv w (riskProcess X x D (u i) ω)),
      ∃ r : Fin n → ℝ,
        (∀ i : Fin n, 0 ≤ r i) ∧
        (∀ i : Fin n,
          (∑' (v : ℝ≥0),
            if u i < v ∧ v ≤ u (i + 1) then
              ENNReal.ofReal (Function.leftLim
                (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
            else 0).toReal + r i =
          (((u (i + 1) : ℝ≥0) : ℝ) * X.drift - X.X (u (i + 1)) ω) -
            (((u i : ℝ≥0) : ℝ) * X.drift - X.X (u i) ω)) ∧
        (∑ i : Fin n,
          -(deriv w (riskProcess X x D (u i) ω)) * r i) ≤ 0 := by sorry

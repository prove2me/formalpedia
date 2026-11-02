-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_one_remainder_partition_variation_and_stopped_limit_nonpos
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_bv_one_remainder_partition_variation_and_stopped_limit_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T11:42:47.595619+00:00
-- url     : https://prove2.me/theorems/e0b95148-74e2-4ed0-8b1d-fdaa7fc14231
-- title:
--   One canonical original BV source residual simultaneously has exact variation and nonpositive stopped C1 approximation limits
-- statement:
--   For the actual bounded-variation spectrally negative Levy source and an admissible dividend strategy, almost surely one uniquely specified residual path R simultaneously has its original drift/jump source formula, monotonicity, exact total variation on every source partition, and a nonpositive real limit for any convergent sequence of stopped derivative-weighted sums from an increasing verification function. This combines two already Proved original-process theorems on one event and one identical R witness; no pure-jump equality or controlled Ito-Meyer integral identification is imposed.
-- source:
--   Chat04-A continuation; import canonically Proved exact BV residual variation 3ddc1a4c-7733-4bfe-82ec-284764e67394 and stopped sum limit sign dc2db8cf-65ec-4ce3-8722-b666f097597a, then prove residual-witness identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_canonical_source_remainder_partition_variation_exact
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_stopped_monotone_verification_remainder_sum_limit_nonpos

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- One source BV residual has exact variation and signs all convergent
stopped C1 derivative-weighted sums, without identifying a stochastic integral. -/

theorem AvramDividend.Classical.avram_wave5_04a_actual_bv_one_remainder_partition_variation_and_stopped_limit_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw : Monotone w) :
    ∀ᵐ ω ∂P, ∃ R : ℝ≥0 → ℝ,
      (∀ t : ℝ≥0,
        R t = ((t : ℝ) * X.drift - X.X t ω) -
          (∑' (v : ℝ≥0),
            if 0 < v ∧ v ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
            else 0).toReal) ∧
      Monotone R ∧
      (∀ (u : ℕ → ℝ≥0) (hu : Monotone u) (n : ℕ),
        (Finset.range n).sum (fun i =>
          |R (u (i + 1)) - R (u i)|) =
        R (u n) - R (u 0)) ∧
      (∀ (τ : Ω → ℝ≥0) (u : ℕ → ℕ → ℝ≥0)
        (hu : ∀ k : ℕ, Monotone (u k))
        (n : ℕ → ℕ) (hstop : ∀ k : ℕ, u k (n k) ≤ τ ω)
        (L : ℝ)
        (hlim : Tendsto (fun k : ℕ =>
          ∑ i : Fin (n k),
            -(deriv w (riskProcess X x D (u k i) ω)) *
              (R (u k (i + 1)) - R (u k i))) atTop (𝓝 L)),
        L ≤ 0) := by sorry

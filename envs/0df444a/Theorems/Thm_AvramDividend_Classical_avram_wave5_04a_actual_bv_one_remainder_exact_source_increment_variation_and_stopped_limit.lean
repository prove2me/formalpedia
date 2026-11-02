-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_one_remainder_exact_source_increment_variation_and_stopped_limit
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_bv_one_remainder_exact_source_increment_variation_and_stopped_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T11:43:49.647526+00:00
-- url     : https://prove2.me/theorems/89718302-b4d0-44e1-9a9f-72eebc913afe
-- title:
--   Single almost-sure original BV residual: exact source jump increments, total variation and sign of convergent stopped C1 sums
-- statement:
--   For the actual original spectrally negative Levy source satisfying bounded variation and an admissible dividend strategy, there is almost surely one explicit source residual R, simultaneously monotone, with exact drift-minus-intrinsic-source-left-jumps-minus-R increments, exact finite variation on every ordered partition, and nonpositive limits of convergent stopped derivative-weighted residual sums for an increasing C1 verification function. No pure-jump equality, independent Poisson construction or controlled Ito-Meyer integration is assumed.
-- source:
--   Chat04-A original-source BV interface; combines canonically Proved exact increment c4b53c7c-d769-4894-a0d8-c0b2a1516d1e, exact variation 3ddc1a4c-7733-4bfe-82ec-284764e67394 and stopped monotone limit dc2db8cf-65ec-4ce3-8722-b666f097597a by uniqueness of the explicit residual.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_exact_interval_increment_from_intrinsic_jumps_and_remainder
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_canonical_source_remainder_partition_variation_exact
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_stopped_monotone_verification_remainder_sum_limit_nonpos

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The single original BV source residual, on one almost-sure event,
has exact intrinsic left-jump increments, exact variation, and stopped
monotone C1 residual limits that are nonpositive. No Ito-Meyer identity. -/

theorem AvramDividend.Classical.avram_wave5_04a_actual_bv_one_remainder_exact_source_increment_variation_and_stopped_limit
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
      (∀ (s t : ℝ≥0) (hst : s ≤ t),
        X.X t ω - X.X s ω =
          ((t : ℝ) - (s : ℝ)) * X.drift -
            (∑' (v : ℝ≥0),
              if s < v ∧ v ≤ t then
                ENNReal.ofReal (Function.leftLim
                  (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
              else 0).toReal -
            (R t - R s)) ∧
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

-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_canonical_source_remainder_stopped_C1_nonpos
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_bv_canonical_source_remainder_stopped_C1_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:34:44.668211+00:00
-- url     : https://prove2.me/theorems/2fa1c0ea-3ed6-4ee9-98bf-4ac6e002d400
-- title:
--   One canonical actual BV downward source remainder contributes nonpositively on every stopped C1 partition
-- statement:
--   For the actual BV spectrally negative Levy process and admissible dividend strategy, almost surely construct the unique explicitly specified source remainder R(t)=t*X.drift-X_t minus the entire real negative source left-jump magnitude series up to t. Establish that R is monotone and for every samplewise stopped finite partition its increments, weighted by the nonnegative C1 verification derivative at the actual controlled reserve samples with a minus sign, have nonpositive total. No pure-jump identity or complete controlled Ito-Meyer theorem is assumed.
-- source:
--   Wave5 Chat04-A. Direct source-coupled signed finite-variation consequence of canonical monotone remainder child 019edf01-4961-4bf1-805e-b935366106bb, subject to that child's Proved status before proof submission.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_canonical_remainder_monotone

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- One canonical monotone actual BV source remainder path has a nonpositive
derivative-weighted finite-variation contribution at every stopped controlled
partition. Source left jumps and chronological right payments stay distinct. -/

theorem AvramDividend.Classical.avram_wave5_04a_actual_bv_canonical_source_remainder_stopped_C1_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (w : ℝ → ℝ) :
    ∀ᵐ ω ∂P, ∃ R : ℝ≥0 → ℝ,
      (∀ t : ℝ≥0,
        R t = ((t : ℝ) * X.drift - X.X t ω) -
          (∑' (u : ℝ≥0),
            if 0 < u ∧ u ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)
            else 0).toReal) ∧
      Monotone R ∧
      ∀ (τ : Ω → ℝ≥0) (u : ℕ → ℝ≥0)
        (hu : Monotone u) (n : ℕ) (hstop : u n ≤ τ ω)
        (hgrad : ∀ i : Fin n,
          0 ≤ deriv w (riskProcess X x D (u i) ω)),
        (∑ i : Fin n,
          -(deriv w (riskProcess X x D (u i) ω)) *
            (R (u (i + 1)) - R (u i))) ≤ 0 := by sorry

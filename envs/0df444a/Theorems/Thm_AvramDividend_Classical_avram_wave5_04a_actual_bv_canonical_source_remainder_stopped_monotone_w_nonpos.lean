-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_canonical_source_remainder_stopped_monotone_w_nonpos
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_bv_canonical_source_remainder_stopped_monotone_w_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:48:31.020365+00:00
-- url     : https://prove2.me/theorems/0f7eed24-7fe4-4ee6-b31f-d400b5655865
-- title:
--   Increasing C1 verification candidates automatically give nonpositive stopped canonical BV source remainder
-- statement:
--   For any monotone increasing real verification function, the genuine original bounded-variation Levy source has an explicitly defined canonical monotone remainder R on one full-probability event, and for every samplewise stopped increasing partition the derivative-weighted negative R-increment sum is nonpositive. The monotone verification function automatically has nonnegative derivative where evaluated by Mathlib's Monotone.deriv_nonneg, so no separate derivative-sign hypothesis is required. No controlled Ito-Meyer integration or pure-jump equality is asserted.
-- source:
--   Avram Wave5 Chat04-A; direct strengthening of canonical stopped C1 sign theorem 2fa1c0ea-3ed6-4ee9-98bf-4ac6e002d400 using pinned Mathlib Monotone.deriv_nonneg.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_canonical_source_remainder_stopped_C1_nonpos

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- For any increasing real verification candidate, the exact actual BV
source remainder contributes nonpositively along every stopped partition;
nonnegativity of its derivative is automatic from monotonicity. -/

theorem AvramDividend.Classical.avram_wave5_04a_actual_bv_canonical_source_remainder_stopped_monotone_w_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw : Monotone w) :
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
        (hu : Monotone u) (n : ℕ) (hstop : u n ≤ τ ω),
        (∑ i : Fin n,
          -(deriv w (riskProcess X x D (u i) ω)) *
            (R (u (i + 1)) - R (u i))) ≤ 0 := by sorry

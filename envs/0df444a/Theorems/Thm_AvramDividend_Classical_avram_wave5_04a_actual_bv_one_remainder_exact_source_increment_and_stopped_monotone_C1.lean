-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_one_remainder_exact_source_increment_and_stopped_monotone_C1
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_bv_one_remainder_exact_source_increment_and_stopped_monotone_C1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T11:38:53.198202+00:00
-- url     : https://prove2.me/theorems/d2ccdfac-1ab5-400a-a251-9c5fe826a0ad
-- title:
--   One genuine BV source residual jointly gives exact intrinsic source increments and stopped increasing-C1 nonpositive contribution
-- statement:
--   For the actual spectrally negative Levy source of bounded variation, on one common probability-one event construct an explicit unique residual R(t) given by source drift minus the source path minus the complete intrinsic negative original left-jump series. Prove this same R is monotone, gives exact drift-minus-jumps-minus-residual source increments over all ordered intervals and yields a nonpositive derivative-weighted residual contribution on every samplewise stopped partition for every increasing verification function. Chronological right dividend payments remain separate; no independent Poisson model, pure-jump identity or controlled Ito-Meyer integration is assumed.
-- source:
--   Wave5 Chat04-A second continuation. Formal conjunction of canonically Proved original-source exact increment c4b53c7c-d769-4894-a0d8-c0b2a1516d1e and monotone stopped sign 0f7eed24-7fe4-4ee6-b31f-d400b5655865; show their existential witnesses are identical by the explicit formula.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_exact_interval_increment_from_intrinsic_jumps_and_remainder
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_canonical_source_remainder_stopped_monotone_w_nonpos

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- One explicit original BV source remainder simultaneously gives
exact intrinsic left-jump increments and the stopped C1 derivative sign
for increasing verification functions; no controlled Ito-Meyer identity. -/

theorem AvramDividend.Classical.avram_wave5_04a_actual_bv_one_remainder_exact_source_increment_and_stopped_monotone_C1
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
      (∀ (τ : Ω → ℝ≥0) (u : ℕ → ℝ≥0)
        (hu : Monotone u) (n : ℕ) (hstop : u n ≤ τ ω),
        (∑ i : Fin n,
          -(deriv w (riskProcess X x D (u i) ω)) *
            (R (u (i + 1)) - R (u i))) ≤ 0) := by sorry

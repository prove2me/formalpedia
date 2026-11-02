-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_stopped_monotone_verification_remainder_sum_limit_nonpos
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_bv_stopped_monotone_verification_remainder_sum_limit_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:51:58.634774+00:00
-- url     : https://prove2.me/theorems/dc2db8cf-65ec-4ce3-8722-b666f097597a
-- title:
--   Any convergent stopped source-BV derivative-weighted remainder sums have nonpositive limit for increasing verification functions
-- statement:
--   For the actual original bounded-variation spectrally negative Levy source, construct one explicit canonical monotone residual R almost surely. Take any sequence of samplewise stopped increasing finite partitions, and evaluate the negative derivative of any monotone increasing real verification function against each increment of R. If this sequence of real signed finite sums converges, its limit is nonpositive. This supplies a limit-stable source contribution interface without assuming that the limit is an Ito-Meyer or Lebesgue-Stieltjes integral.
-- source:
--   Wave5 Chat04-A; imports the Proved monotone-verification stopped source sign helper and pinned Mathlib le_of_tendsto. Publish only after imported monotone-verification helper is Proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_canonical_source_remainder_stopped_monotone_w_nonpos

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Any real limit of stopped derivative-weighted original BV remainder
sums is nonpositive when w is increasing. This does not identify the limit
with an Itô or Stieltjes integral. -/

theorem AvramDividend.Classical.avram_wave5_04a_actual_bv_stopped_monotone_verification_remainder_sum_limit_nonpos
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
      ∀ (τ : Ω → ℝ≥0) (u : ℕ → ℕ → ℝ≥0)
        (hu : ∀ k : ℕ, Monotone (u k))
        (n : ℕ → ℕ) (hstop : ∀ k : ℕ, u k (n k) ≤ τ ω)
        (L : ℝ)
        (hlim : Tendsto (fun k : ℕ =>
          ∑ i : Fin (n k),
            -(deriv w (riskProcess X x D (u k i) ω)) *
              (R (u k (i + 1)) - R (u k i))) atTop (𝓝 L)),
        L ≤ 0 := by sorry

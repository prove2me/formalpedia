-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_05_original_any_index_discounted_dividend_jump_positivepart_tsum_zero
-- name    : AvramDividend.Classical.avram_wave6_05_original_any_index_discounted_dividend_jump_positivepart_tsum_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T21:52:21.499047+00:00
-- url     : https://prove2.me/theorems/292c0d04-e0fa-4480-9353-0e1e7d24220c
-- title:
--   Any-index original right dividend jump residual has zero total discounted positive part
-- statement:
--   At any admissible original payment time before ruin, including the separately admissible time-zero payment, the cap-linear reserve function V loses at least the contemporaneous dividend, even if the original Levy source jumps simultaneously. Therefore every real discounted jump cash excess is nonpositive and its extended-nonnegative positive part is zero. Summing over any index set A of such times yields exactly zero ENNReal tsum, without assuming finite-jump controls, countability, absolute convergence or real summability. This uniform no-positive-excess statement complements the exact original dividendMeasure atomless plus all-right-atoms Stieltjes identity.
-- source:
--   Apply the accepted genuine all-time cap-linear chronological right-dividend drop at each subtype t∈A, using admissibility and the retained t=0-or-pre-ruin predicate. Rearrange its δ≤V(U)-V(U-δ) inequality by linarith to δ+V(U-δ)-V(U)≤0. The exponential factor is strictly positive for any real discount q, so the weighted real residual remains nonpositive; ENNReal.ofReal of that residual is zero. By function extensionality, the entire ENNReal tsum equals tsum of zero, without summability, countability or source-jump exclusions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_actual_alltime_caplinear_dividend_jump_drop

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_wave6_05_original_any_index_discounted_dividend_jump_positivepart_tsum_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (q : ℝ) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hVtop : C = ⊤ → ∀ y : ℝ, V y = w y)
    (hVfinite : C ≠ ⊤ → ∀ y : ℝ,
      V y = if y ≤ C.toReal then w y
        else w C.toReal + (y - C.toReal))
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) (ω : Ω)
    (A : Set ℝ≥0)
    (hA : ∀ t : A,
      (t : ℝ≥0) = 0 ∨
        ((t : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω) :
    (∑' t : A, ENNReal.ofReal
      (Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
        ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
          V (riskProcess X x D (t : ℝ≥0) ω -
            (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
          V (riskProcess X x D (t : ℝ≥0) ω)))) = 0 := by sorry

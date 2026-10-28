-- Prove2me | Theorems.Thm_AvramDividend_Classical_zero_reflectedSupValue_of_ae_early_downward_jumps_and_deriv_top
-- name    : AvramDividend.Classical.zero_reflectedSupValue_of_ae_early_downward_jumps_and_deriv_top
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T20:57:52.213711+00:00
-- url     : https://prove2.me/theorems/9228cae3-d9ad-43aa-a273-f053d812bfaa
-- title:
--   Zero reflected-supremum identity from early Lévy downward jumps and infinite scale derivative
-- statement:
--   If almost every Lévy sample path has a strict negative jump arbitrarily close to the initial time, then the canonical downward-jump lemma gives immediate reflected ruin. The existing verified instant-ruin dividend-reward theorem and infinite-scale-slope zero-value theorem then establish equality of the stochastic and analytic zero-barrier values. This is a direct conditional bridge for infinite-activity negative-jump processes.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1, equation (3.13) and zero-barrier discussion, https://arxiv.org/pdf/math/0702893

import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_zero_of_early_downward_jumps
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_zero_of_ae_instant_ruin
import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_of_derivZeroPlus_top

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- Almost-sure downward jumps near zero and an infinite scale slope imply the zero-barrier value identity. -/
theorem zero_reflectedSupValue_of_ae_early_downward_jumps_and_deriv_top
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (W : ℝ → ℝ)
    (hJumps : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, 0 < t ∧ t < ε ∧
        ∃ l : ℝ,
          Tendsto (fun s : ℝ≥0 => X.X s ω) (nhdsWithin t (Iio t)) (nhds l) ∧
          X.X t ω < l)
    (hder : derivZeroPlus W = ⊤) :
    barrierSupValue X 0 q = ENNReal.ofReal (barrierValue W 0 0) := by sorry

end AvramDividend.Classical

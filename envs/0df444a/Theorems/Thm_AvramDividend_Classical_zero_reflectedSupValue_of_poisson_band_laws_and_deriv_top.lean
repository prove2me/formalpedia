-- Prove2me | Theorems.Thm_AvramDividend_Classical_zero_reflectedSupValue_of_poisson_band_laws_and_deriv_top
-- name    : AvramDividend.Classical.zero_reflectedSupValue_of_poisson_band_laws_and_deriv_top
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:11:47.07216+00:00
-- url     : https://prove2.me/theorems/c8d5dc23-9382-49b8-90d4-2a9aba6d56ce
-- title:
--   Zero-barrier reflected-supremum value from two-index Poisson jump-count laws and infinite scale derivative
-- statement:
--   For each horizon δ_k shrinking to zero, suppose finite-band negative-jump counts indexed by n have Poisson zero-count probabilities exp(-rates k n), with rates diverging in n, and absence of a negative path jump before δ_k entails zero counts in every truncated band. The established null-count lemma proves absence of a jump is null for each k; the countable-grid theorem yields almost-sure jumps arbitrarily near zero; the established instant-ruin and infinite-scale-slope identity then give the full reflected-supremum zero-barrier equality. The remaining task is deriving the two-index count law and the scale-derivative boundary from the Lévy model.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1 and (3.13), https://arxiv.org/pdf/math/0702893; three established Prove2Me conditional prerequisites.

import Theorems.Thm_AvramDividend_Classical_zero_probability_of_poisson_count_no_jump_event
import Theorems.Thm_AvramDividend_Classical_ae_early_downward_jumps_of_null_no_jump_grid
import Theorems.Thm_AvramDividend_Classical_zero_reflectedSupValue_of_ae_early_downward_jumps_and_deriv_top

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- Poisson laws for shrinking initial intervals and infinite scale slope imply the zero-barrier identity. -/
theorem zero_reflectedSupValue_of_poisson_band_laws_and_deriv_top
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (W : ℝ → ℝ)
    (δ : ℕ → ℝ≥0) (counts : ℕ → ℕ → Ω → ℕ)
    (rates : ℕ → ℕ → ℝ)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε → ∃ k : ℕ, δ k < ε)
    (hdiv : ∀ k : ℕ, Tendsto (rates k) atTop atTop)
    (hsubset : ∀ k n : ℕ,
      {ω : Ω | ¬ ∃ t : ℝ≥0, 0 < t ∧ t < δ k ∧
        ∃ l : ℝ, Tendsto (fun s : ℝ≥0 => X.X s ω)
          (nhdsWithin t (Iio t)) (nhds l) ∧ X.X t ω < l}
        ⊆ {ω | counts k n ω = 0})
    (hzeroLaw : ∀ k n : ℕ,
      P {ω | counts k n ω = 0} =
        ENNReal.ofReal (Real.exp (-(rates k n))))
    (hder : derivZeroPlus W = ⊤) :
    barrierSupValue X 0 q = ENNReal.ofReal (barrierValue W 0 0) := by sorry

end AvramDividend.Classical

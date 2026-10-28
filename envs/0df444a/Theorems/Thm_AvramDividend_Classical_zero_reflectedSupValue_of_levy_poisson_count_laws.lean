-- Prove2me | Theorems.Thm_AvramDividend_Classical_zero_reflectedSupValue_of_levy_poisson_count_laws
-- name    : AvramDividend.Classical.zero_reflectedSupValue_of_levy_poisson_count_laws
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:49:45.119845+00:00
-- url     : https://prove2.me/theorems/3d156c7e-4439-4646-8e55-61f536384a54
-- title:
--   Zero-barrier reflected value from actual Lévy-band Poisson laws and infinite scale derivative
-- statement:
--   For a spectrally negative Lévy process whose negative Lévy measure has infinite activity, consider positive horizons tending to zero. Suppose its finite-band jump count variables have Poisson zero-count laws with parameters δ_k times the actual truncated Lévy measure, and zero path jumps implies zero counts. The proven truncated Lévy intensity theorem supplies divergent rates automatically; the proven Poisson count and early-jump argument establishes instantaneous ruin, giving zero reflected value when the scale right derivative is infinite. This removes the arbitrary divergent-rate hypothesis of the earlier conditional reduction.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1, zero-barrier equation (3.13), https://arxiv.org/pdf/math/0702893; proved Prove2Me Lévy-intensity and conditional Poisson-band results.

import Theorems.Thm_AvramDividend_Classical_zero_reflectedSupValue_of_poisson_band_laws_and_deriv_top
import Theorems.Thm_AvramDividend_Classical_negative_jump_real_poisson_rates_tendsto_top

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- Lévy-measure infinite activity supplies the divergent rates in the Poisson-band argument. -/
theorem zero_reflectedSupValue_of_levy_poisson_count_laws
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (W : ℝ → ℝ)
    (δ : ℕ → ℝ≥0) (counts : ℕ → ℕ → Ω → ℕ)
    (hνinf : X.ν (Iio (0 : ℝ)) = ⊤)
    (hδpos : ∀ k : ℕ, 0 < δ k)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε → ∃ k : ℕ, δ k < ε)
    (hsubset : ∀ k n : ℕ,
      {ω : Ω | ¬ ∃ t : ℝ≥0, 0 < t ∧ t < δ k ∧
        ∃ l : ℝ, Tendsto (fun s : ℝ≥0 => X.X s ω)
          (nhdsWithin t (Iio t)) (nhds l) ∧ X.X t ω < l}
        ⊆ {ω | counts k n ω = 0})
    (hzeroLaw : ∀ k n : ℕ,
      P {ω | counts k n ω = 0} =
        ENNReal.ofReal (Real.exp
          (-((δ k : ℝ) *
            (X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal))))
    (hder : derivZeroPlus W = ⊤) :
    barrierSupValue X 0 q = ENNReal.ofReal (barrierValue W 0 0) := by sorry

end AvramDividend.Classical

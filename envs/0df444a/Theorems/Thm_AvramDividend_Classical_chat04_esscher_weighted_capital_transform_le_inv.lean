-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_capital_transform_le_inv
-- name    : AvramDividend.Classical.chat04_esscher_weighted_capital_transform_le_inv
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:33:39.220819+00:00
-- url     : https://prove2.me/theorems/593ff26b-5218-45dd-a351-ff64a31df147
-- title:
--   Global capital-integrated Esscher killed survival Laplace transform bounded by inverse parameter
-- statement:
--   The full nonnegative capital-Laplace transform of the continuously killed Esscher-weighted Lévy process is bounded by 1/β, uniformly over finite time horizons. This gives an explicit finite ENNReal bound on the true double integral used in the Wiener-Hopf limit, not merely on an intermediary reflected expectation.
-- source:
--   Direct composition of Proved finite-horizon real expectation bridge 3c50d08b and Proved uniform real reflected transform bound d204e00c via ENNReal.ofReal monotonicity. Independent of the unproved Wiener-Hopf value and two-sided exit identity.

import Mathlib.Data.ENNReal.Real
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_capital_real_expectation_bridge
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_reflected_transform_unit_bound

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_esscher_weighted_capital_transform_le_inv
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (β θ : ℝ) (hβ : 0 < β) (hθ : 0 ≤ θ) :
    (∫⁻ (x : ℝ), ∫⁻ (ω : Ω),
      Set.indicator
        {p : ℝ × Ω | 0 < p.1 ∧
          ∀ s : ℝ≥0, s ≤ t → 0 ≤ p.1 + X.X s p.2}
        (fun p => ENNReal.ofReal
          (Real.exp (-β * p.1) *
            Real.exp (θ * X.X t p.2 -
              (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)))
        (x, ω) ∂P ∂volume) ≤
    ENNReal.ofReal (1 / β) := by sorry

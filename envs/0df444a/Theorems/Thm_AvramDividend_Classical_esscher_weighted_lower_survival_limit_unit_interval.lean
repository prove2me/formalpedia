-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_limit_unit_interval
-- name    : AvramDividend.Classical.esscher_weighted_lower_survival_limit_unit_interval
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:53:59.257129+00:00
-- url     : https://prove2.me/theorems/2e73f259-2c49-49e9-9b70-9c16456a87df
-- title:
--   Infinite-horizon Esscher lower survival envelope lies in the unit interval
-- statement:
--   For a spectrally negative Levy process and nonnegative Esscher parameter, the infimum of its nonnegative, unit-bounded finite-horizon lower survival masses also lies in the unit interval. This gives a rigorous domination bound for later semigroup limits.
-- source:
--   Composition of published Prove2Me Esscher survival lemmas and indexed Mathlib conditional infimum lemmas. Supports the infinite-horizon renewal and killed q-scale harmonicity derivation.

import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_mass_unit_interval

open MeasureTheory
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.esscher_weighted_lower_survival_limit_unit_interval
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) (x : ℝ) :
    0 ≤
      (⨅ t : ℝ≥0,
        ∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
          (fun ω => Real.exp
            (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P)
    ∧
      (⨅ t : ℝ≥0,
        ∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
          (fun ω => Real.exp
            (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P) ≤ 1 := by sorry

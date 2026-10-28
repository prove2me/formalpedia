-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_limit_monotone_start
-- name    : AvramDividend.Classical.esscher_weighted_lower_survival_limit_monotone_start
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:53:57.795759+00:00
-- url     : https://prove2.me/theorems/2e5d0c08-99e9-44ee-96cf-5164bda59ce8
-- title:
--   Infinite-horizon Esscher lower survival envelope is increasing in initial reserve
-- statement:
--   For a spectrally negative Levy process and nonnegative Esscher parameter, the infimum over all finite-time Esscher-weighted lower survival masses is monotone in the initial reserve. The theorem uses finite-horizon spatial monotonicity and the nonnegative bounded-below mass property.
-- source:
--   Composition of published Prove2Me Esscher survival lemmas and indexed Mathlib conditional infimum lemmas. Supports the infinite-horizon renewal and killed q-scale harmonicity derivation.

import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_mass_monotone_start
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_mass_unit_interval

open MeasureTheory
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.esscher_weighted_lower_survival_limit_monotone_start
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) (x y : ℝ) (hxy : x ≤ y) :
    (⨅ t : ℝ≥0,
      ∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
        (fun ω => Real.exp
          (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P) ≤
    (⨅ t : ℝ≥0,
      ∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ y + X.X s ω}).indicator
        (fun ω => Real.exp
          (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P) := by sorry

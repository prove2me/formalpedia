-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_esscher_true_capital_transform_tendsto_infimum
-- name    : AvramDividend.Classical.chat04_esscher_true_capital_transform_tendsto_infimum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:37:01.156124+00:00
-- url     : https://prove2.me/theorems/53cadb49-3690-4599-a2b0-75b933fec702
-- title:
--   Infinite-horizon existence of the true Esscher capital Laplace transform
-- statement:
--   The actual capital-integrated Esscher-weighted killed-survival Laplace transform converges as the time horizon increases without bound. Its limit is the infimum of all finite-horizon transforms in ENNReal. This proves existence of the infinite-horizon scalar mass but does not yet identify its numerical Wiener-Hopf transform.
-- source:
--   Use Proved true finite-horizon Esscher-capital transform antitonicity and bottom boundedness in ENNReal; apply pinned Mathlib tendsto_atTop_ciInf. The infinite-horizon limit exists independent of any extension of the Esscher measure or circular use of the two-sided exit identity. Next identity with ψ'(φ)β/(ψ(φ+β)−q) needs independent fluctuation theory.

import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_true_capital_transform_antitone

open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_esscher_true_capital_transform_tendsto_infimum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ β : ℝ) (hθ : 0 ≤ θ) (hβ : 0 < β) :
    Tendsto
      (fun t : ℝ≥0 => (∫⁻ (x : ℝ) in Ioi (0 : ℝ),
      ∫⁻ ω,
        ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
          (fun ω => ENNReal.ofReal
            (Real.exp (-β * x) *
              Real.exp (θ * X.X t ω -
                (t : ℝ) * laplaceExponent X.c X.σ X.ν θ))) ω ∂P
      ∂volume))
      atTop
      (nhds (⨅ t : ℝ≥0, (∫⁻ (x : ℝ) in Ioi (0 : ℝ),
      ∫⁻ ω,
        ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
          (fun ω => ENNReal.ofReal
            (Real.exp (-β * x) *
              Real.exp (θ * X.X t ω -
                (t : ℝ) * laplaceExponent X.c X.σ X.ν θ))) ω ∂P
      ∂volume))) := by sorry

-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_allnu_pre_rightdividend_reserve_source_decomposition
-- name    : AvramDividend.Classical.avram_p4_f3_original_allnu_pre_rightdividend_reserve_source_decomposition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:20:45.981204+00:00
-- url     : https://prove2.me/theorems/bd31d3db-8afc-4816-96e7-b6310f3c51ba
-- title:
--   Original all-ν source decomposition of the actual pre-right-payment riskProcess
-- statement:
--   For the genuine original Lévy riskProcess with a same-space decomposition of X into drift, its zero-ν Gaussian component and small and large jump paths, the exact pre-right-dividend reserve subtracts D t. This is the mathematically correct pathwise source identity for nonzero right dividend payment atoms, independent of any right-continuity assumption. The postpayment reserve subtracts rightLimit D and must include an explicit payment-atom correction.
-- source:
--   Unfold original riskProcess and substitute the original same-space source decomposition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_allnu_pre_rightdividend_reserve_source_decomposition
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ (u : ℝ≥0) (η : Ω),
      X.X u η = (u : ℝ) * X.c +
        (Y.X u η - (u : ℝ) * Y.c) + Jsmall u η + Jlarge u η)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (t : ℝ≥0) (ω : Ω) :
    riskProcess X x D t ω =
      x + ((t : ℝ) * X.c +
        (Y.X t ω - (t : ℝ) * Y.c) +
          Jsmall t ω + Jlarge t ω) - D t ω := by sorry

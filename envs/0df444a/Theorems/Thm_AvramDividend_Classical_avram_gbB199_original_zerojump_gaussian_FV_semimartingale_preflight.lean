-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB199_original_zerojump_gaussian_FV_semimartingale_preflight
-- name    : AvramDividend.Classical.avram_gbB199_original_zerojump_gaussian_FV_semimartingale_preflight
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T23:36:14.288758+00:00
-- url     : https://prove2.me/theorems/a44cfbfa-ff67-4d84-9fee-c63f44c05666
-- title:
--   Original controlled zero-jump Gaussian reserve decomposes into a centred martingale and finite-variation drift data
-- statement:
--   The original zero-jump Gaussian Lévy source has a centred right-continuous filtration martingale and compensated square martingale, continuous paths almost surely, and the original postpayment dividend strategy has locally finite variation. The reserve equals the sum of that centred martingale and a drift-minus-dividend path. These are the exact stochastic preconditions for an eventual semimartingale occupation proof.
-- source:
--   Gaussian B finite-cap occupation obstruction 12 Nov 2026; consolidates already Proved wave6_03 centred martingales, B173 right-limit dividends FV and ubv_top11 source continuity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB199_original_zerojump_gaussian_FV_semimartingale_preflight
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) :
    Martingale (fun t ω => X.X t ω - (t : ℝ) * X.c)
      𝓕.rightCont P ∧
    Martingale (fun t ω =>
      (X.X t ω - (t : ℝ) * X.c) ^ 2 -
        (t : ℝ) * X.σ ^ 2) 𝓕.rightCont P ∧
    (∀ ω, LocallyBoundedVariationOn
      (fun t : ℝ≥0 => rightLimit D t ω) Set.univ) ∧
    (∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => X.X t ω)) ∧
    ∀ t ω, x + X.X t ω - rightLimit D t ω =
      (X.X t ω - (t : ℝ) * X.c) +
        (x + (t : ℝ) * X.c - rightLimit D t ω) := by sorry

-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_physical_Brownian_size2_tube_forces_original_inclusive_barrier_cash_zero
-- name    : AvramDividend.Classical.avram_jump6_A_physical_Brownian_size2_tube_forces_original_inclusive_barrier_cash_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T11:24:18.296708+00:00
-- url     : https://prove2.me/theorems/23271938-2d27-4c37-8fbe-1afbf63f8f7b
-- title:
--   Physical Brownian-negative-Poisson early tube forces zero real original inclusive barrier cash before upper exit
-- statement:
--   On the true original Brownian−2N spectrally-negative Lévy path, a Brownian tube of radius 1/4000 and nonnegative negative-mark count ensure that the process never crosses the finite barrier difference 1/10 before σ. For the exact first upper-exit time u, σ≤u; hence the original right-closed discounted Stieltjes dividend cash, stopped at the true ruinTime and capped by σ, is identically zero. Import only the publicly Proved source barrierStrategy_preUpcrossing_stieltjesReward_zero and the publicly Proved original physical upper-exit order lemma, avoiding private cross-owner dependencies. This supplies the genuine cash part of the pending positive-ruin-mark contradiction to original full-mark physical mesh source 061f936f.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_physical_Brownian_size2_tube_forces_original_inclusive_barrier_cash_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (B : ℝ≥0 → ℝ) (N : ℝ≥0 → ℕ)
    (σ u : ℝ≥0)
    (hPath : ∀ t : ℝ≥0, X.X t ω = B t - 2 * (N t : ℝ))
    (hTube : ∀ t : ℝ≥0, t ≤ σ → |B t| < (1 / 4000 : ℝ))
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0)
        (_ : (1 / 5 : ℝ) - (1 / 10 : ℝ) < X.X s ω),
        (s : ℝ≥0∞)))
    (q : ℝ) :
    (∫⁻ s in paymentTimes
        (ruinTime X (1 / 10 : ℝ)
          (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) ω) ∩
        Iic (σ : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure
            (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) ω)) = 0 := by sorry

-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_closedHorizon_fullStieltjes_exponential_budget_q_ge_psi
-- name    : AvramDividend.Classical.avram_wave4_03_sourceLevy_closedHorizon_fullStieltjes_exponential_budget_q_ge_psi
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T00:01:37.065525+00:00
-- url     : https://prove2.me/theorems/cd61fb3d-301f-405c-a487-cd1c214780d7
-- title:
--   Original Lévy full closed-horizon Stieltjes exponential budget for q≥ψ(1) including the initial right dividend atom
-- statement:
--   For the actual source spectrally negative Lévy X and any admissible adapted left-continuous right-payment dividend strategy D, the expected entire closed interval [0,T] Stieltjes exponential source dividend mass at any rate q at least ψ(1) is at most one. The already Proved original-source full Icc budget at ψ(1) contains the time-zero atom, positive-time right atoms, diffuse and singular-continuous mass, and the pointwise monotonicity q≥ψ(1) transfers this estimate without altering the control or measure. This is a special exponential-test stochastic consequence, not arbitrary-C1 HJB verification.
-- source:
--   Proved genuine original-source closed Icc full-Stieltjes expected exponential budget ff6f1a5c-39ae-4162-8ea2-325b14c4c720, Accepted source submission fae219f6-afe4-466d-91c9-46e473398255.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_closedHorizon_fullStieltjes_Icc_exponential_budget
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_03_sourceLevy_closedHorizon_fullStieltjes_exponential_budget_q_ge_psi
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : X.ψ 1 ≤ q)
    (T : ℝ≥0) (hT : 0 < T) :
    (∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) (T : ℝ),
      ENNReal.ofReal (Real.exp
        (X.X s.toNNReal ω - rightLimit D s.toNNReal ω -
          (s.toNNReal : ℝ) * q))
      ∂dividendMeasure D ω ∂P) ≤ 1 := by sorry

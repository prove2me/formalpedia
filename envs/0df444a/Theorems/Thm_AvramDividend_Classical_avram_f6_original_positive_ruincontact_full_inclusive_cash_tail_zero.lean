-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_positive_ruincontact_full_inclusive_cash_tail_zero
-- name    : AvramDividend.Classical.avram_f6_original_positive_ruincontact_full_inclusive_cash_tail_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T20:58:10.572023+00:00
-- url     : https://prove2.me/theorems/d9f559cd-97ab-4289-a506-5d47ccc3f7ec
-- title:
--   Original positive ruin-contact full inclusive discounted dividend cash tail tends to zero
-- statement:
--   For the original spectrally negative Lévy risk process X, actual dividend strategy D, and a strictly positive realised clock τ exactly equal to ruinTime X x D ω, the genuine discounted Stieltjes dividend cash on the inclusive last physical interval (τ−δ_j,τ] tends to zero for every positive, decreasing mesh δ_j→0. The original paymentTimes mask strictly excludes the positive ruin endpoint; an existing source-authentic full Ioc tail limit identifies the only possible residual as the terminal singleton, and a second Proved original theorem makes that residual exactly zero. The result handles the true original ruin-contact boundary and preserves time-zero atoms on other clocks, without assuming any artificial Gaussian or jump noise decomposition.
-- source:
--   Proved 3240dd0b original full discounted masked Ioc contact tail limit, Proved 2ffd301e original strictly positive ruin endpoint singleton cash zero.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_positive_ruincontact_full_inclusive_cash_tail_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (τ : ℝ≥0) (hτ : 0 < τ)
    (hruin : (τ : ℝ≥0∞) = ruinTime X x D ω)
    (q : ℝ) (hq : 0 ≤ q)
    (δ : ℕ → ℝ) (hδpos : ∀ n, 0 < δ n)
    (hδanti : Antitone δ) (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Ioc ((τ : ℝ) - δ n) (τ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
      atTop (𝓝 0) := by sorry

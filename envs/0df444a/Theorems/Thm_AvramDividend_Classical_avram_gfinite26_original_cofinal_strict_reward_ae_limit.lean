-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gfinite26_original_cofinal_strict_reward_ae_limit
-- name    : AvramDividend.Classical.avram_gfinite26_original_cofinal_strict_reward_ae_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T03:23:56.854139+00:00
-- url     : https://prove2.me/theorems/13b754f2-62d3-4b36-ac1c-ae647723ab2a
-- title:
--   Original zero-jump strict stopped reward converges under any cap and monotone physical clocks
-- statement:
--   Root-connected finite-cap convergence child of 3308ae9d. Continuous zero-jump original paths, left-continuous original dividends and the strict-cash monotone convergence theorem imply almost-everywhere convergence of the full original strict stopped reward from any monotone a.e. cofinal clock family. No top-cap or nonzero Gaussian assumption is needed for the pathwise assertion.
-- source:
--   The entire proof tactic body is exactly the accepted source of Proved 8094a1e4 with unused hypotheses eliminated; imports source continuous-path, strict pre-ruin nonnegativity and real strict cash cofinality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top11_original_zero_nu_global_continuous_ae
import Theorems.Thm_AvramDividend_Classical_riskProcess_nonnegative_strictly_before_ruin
import Theorems.Thm_AvramDividend_Classical_avram_gclose17_original_strict_cash_real_monotone_cofinal_clock
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_truncated_clock_nnreal_bounds
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gfinite26_original_cofinal_strict_reward_ae_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hNuZero : X.ν = 0)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (σ : Ω → ℝ≥0) (hσle : ∀ ω, σ ω ≤ τ ω)
    (ρ : ℕ → Ω → ℝ≥0)
    (hρle : ∀ j ω, ρ j ω ≤ σ ω)
    (hρmono : ∀ ω, Monotone (fun j : ℕ => ρ j ω))
    (hρlim : ∀ᵐ ω ∂P, Tendsto (fun j => ρ j ω) atTop (nhds (σ ω))) :
    let H : (Ω → ℝ≥0) → Ω → ℝ := fun ζ ω => if ζ ω = 0 then w x else Real.exp (-(q * (ζ ω : ℝ))) * w (riskProcess X x D (ζ ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ζ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal
    ∀ᵐ ω ∂P, Tendsto (fun j => ENNReal.ofReal (H (ρ j) ω)) atTop (nhds (ENNReal.ofReal (H σ ω))) := by sorry

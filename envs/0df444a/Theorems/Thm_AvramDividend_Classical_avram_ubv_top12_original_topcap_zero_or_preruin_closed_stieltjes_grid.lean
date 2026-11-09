-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_top12_original_topcap_zero_or_preruin_closed_stieltjes_grid
-- name    : AvramDividend.Classical.avram_ubv_top12_original_topcap_zero_or_preruin_closed_stieltjes_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T12:23:56.206652+00:00
-- url     : https://prove2.me/theorems/e6a7a3bc-383f-4e99-a2ce-6d39df2ec1f3
-- title:
--   Original infinite-cap stopped Stieltjes dividend grid bound with initial atom and vanishing mesh error
-- statement:
--   For C equal to infinity, specialise the original-process clipped Stieltjes grid theorem to the true value function w. At a zero or strictly pre-ruin clock the inclusive stopped dividend cash is bounded by the time-zero dividend atom plus discounted true-w reserve drops across a refining grid and a nonnegative error converging to zero. This retains singular continuous dividends and right-payment jumps.
-- source:
--   Specialises Proved a9e5a0ec under C=⊤ with the finite-cap continuation V=w, preserving the full original clipped-grid budget and zero-mesh result.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped Topology NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_top12_original_topcap_zero_or_preruin_closed_stieltjes_grid
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTop : C = ⊤)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (τ : Ω → ℝ≥0) (T : ℝ≥0)
    (hτT : τ ω ≤ T)
    (hPre : τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω)
    (u : ℕ → ℕ → ℝ≥0) (hu : ∀ n, Monotone (u n))
    (k : ℕ → ℕ) (hzero : ∀ n, u n 0 = 0)
    (hcover : ∀ n, τ ω ≤ u n (k n))
    (mesh : ℕ → ℝ) (hm : ∀ n, 0 ≤ mesh n)
    (hmesh : ∀ n i, i < k n →
      ((u n (i + 1) : ℝ) - (u n i : ℝ)) ≤ mesh n)
    (hmesh0 : Tendsto mesh atTop (𝓝 0)) :
    (let v : ℕ → ℕ → ℝ≥0 := fun n i => min (u n i) (τ ω)
     (∀ n,
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal (rightLimit D 0 ω) * ENNReal.ofReal (Real.exp (-(q * 0))) +
      ((∑ i ∈ Finset.range (k n),
        ENNReal.ofReal (Real.exp (-(q * (v n (i + 1) : ℝ)))) *
          ENNReal.ofReal
            (w (x + X.X (v n (i + 1)) ω - rightLimit D (v n i) ω) -
             w (x + X.X (v n (i + 1)) ω - rightLimit D (v n (i + 1)) ω))) +
        ENNReal.ofReal (q * mesh n) *
          dividendMeasure D ω (Ioc (0 : ℝ) (τ ω : ℝ)))) ∧
     Tendsto
       (fun n => (ENNReal.ofReal (q * mesh n) *
         dividendMeasure D ω (Ioc (0 : ℝ) (τ ω : ℝ))).toReal)
       atTop (𝓝 0)) := by sorry

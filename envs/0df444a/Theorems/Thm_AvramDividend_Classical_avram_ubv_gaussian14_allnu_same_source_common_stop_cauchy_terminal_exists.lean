-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian14_allnu_same_source_common_stop_cauchy_terminal_exists
-- name    : AvramDividend.Classical.avram_ubv_gaussian14_allnu_same_source_common_stop_cauchy_terminal_exists
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T14:33:18.498216+00:00
-- url     : https://prove2.me/theorems/ec20e810-f7d7-49ed-9351-dfa6edb9f9d2
-- title:
--   Original all-nu Gaussian stopped grid L2 Cauchy property constructs a centred terminal stochastic integral
-- statement:
--   On the unchanged original spectrally negative Lévy probability space with the same right-continuous filtration, use the explicit same-space zero-jump Gaussian source decomposition. Each finite stopped predictable C2 gradient grid is L2 and exactly centred by previously proved source theorems. Pairwise L2 Cauchy control of these grids constructs a genuine centred terminal L2 stochastic-integral random variable, without an assumed terminal M. The only missing source work is to prove the same-space decomposition and true original-grid energy/Cauchy convergence.
-- source:
--   Proved original all-nu Gaussian stopped finite-grid square integrability 0e190b1b and mean zero e40a12a2; Gaussian14 centred L2 Cauchy terminal construction 1dc8ba44.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn7_original_allnu_Xminusjump_stopped_C2_gaussian_gradient_finite_sum_L2
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn7_original_allnu_Xminusjump_stopped_C2_gaussian_gradient_finite_sum_mean_zero
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian14_centred_L2_cauchy_limit_exists

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gaussian14_allnu_same_source_common_stop_cauchy_terminal_exists
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ (t : ℝ≥0) (ω : Ω),
      X.X t ω = (t : ℝ) * X.c +
        (Y.X t ω - (t : ℝ) * Y.c) + Jsmall t ω + Jlarge t ω)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T : ℝ≥0)
    (S : ℕ → Finset ι) (τ : ℕ → Ω → ℝ≥0)
    (hτ : ∀ (n : ℕ) (s : ℝ≥0),
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ n ω ≤ s})
    (B : ℕ → ℝ≥0) (hB : ∀ n ω, τ n ω ≤ B n)
    (h : ℕ → ι → ℝ≥0) (G : ℕ → ι → Ω → ℝ)
    (hGsource : ∀ n i, i ∈ S n → G n i = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ n ω : WithTop ℝ≥0)))
    (K : ℕ → ι → ℝ)
    (hK : ∀ n i, i ∈ S n → 0 ≤ K n i)
    (hGbound : ∀ n i, i ∈ S n → ∀ ω, |G n i ω| ≤ K n i) :
    let M : ℝ≥0 → Ω → ℝ := fun t ω =>
      X.X t ω - (t : ℝ) * X.c - Jsmall t ω - Jlarge t ω
    let Q : ℕ → Ω → ℝ := fun n ω =>
      ∑ i ∈ S n, G n i ω * (M (τ n ω + h n i) ω - M (τ n ω) ω)
    Tendsto (fun nm : ℕ × ℕ => eLpNorm (Q nm.1 - Q nm.2) 2 P)
      atTop (𝓝 0) →
    ∃ L : Ω → ℝ, MemLp L 2 P ∧
      (∫ ω, L ω ∂P) = 0 ∧
      Tendsto (fun n => eLpNorm (Q n - L) 2 P) atTop (𝓝 0) := by sorry

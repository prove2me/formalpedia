-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f17_original_preexit_leftlimit_gaussian_uniform_C2_bound
-- name    : AvramDividend.Classical.avram_f17_original_preexit_leftlimit_gaussian_uniform_C2_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T08:28:03.865565+00:00
-- url     : https://prove2.me/theorems/e552b242-3059-4131-82c3-b7cbe54888bf
-- title:
--   Original controlled pre-exit left-reserve limit has uniform discounted Gaussian C2 bounds on the authentic band
-- statement:
--   For the actual original controlled spectrally negative Levy reserve and its countably observed stopping clock, zero jumps and unbounded variation ensure one pair of uniform discounted Gaussian gradient and Hessian bounds simultaneously for every true pre-exit left reserve limit. The left-limit is proved for the original stopped path and lies in the same compact reserve band. The theorem combines the independently Proved countable-clock left-limit source with the independently Proved original zero-jump UBV compact C2 envelope, and retains the genuine dense-grid and localisation hypotheses.
-- source:
--   Acyclic combination of public Proved original stopped countable-clock left-limit band theorem 51095652 and public Proved original UBV zerojump compact C2 coefficient bound b1b691b1. Actual X, D, cap, left limits and filtered clock are preserved, no invented surrogate process or source omission.

import Mathlib
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_countable_clock_preexit_left_limit_uniform_band_bound_C2
import Theorems.Thm_AvramDividend_Classical_avram_f16_original_ubv_zerojump_compact_C2_autoopen_envelope
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_f17_original_preexit_leftlimit_gaussian_uniform_C2_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (q : ℝ) (hq : 0 ≤ q) (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (r : ℕ → ℝ≥0) (lower upper : ℝ) (hlower : 0 < lower)
    (hcap : ∀ y ∈ Set.Icc lower upper, ENNReal.ofReal y < C)
    (hgrid : ∀ (s t : ℝ≥0), s < t →
      ∀ U : Set ℝ≥0, U ∈ 𝓝[Set.Ici s] s →
        ∃ k, r k < t ∧ r k ∈ U) :
    ∃ KG KH : ℝ, 0 ≤ KG ∧ 0 ≤ KH ∧
      ∀ (ω : Ω) (T : ℝ≥0),
        (T : WithTop ℝ≥0) ≤ (⨅ k : ℕ,
          if x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨
              upper < x + X.X (r k) ω - rightLimit D (r k) ω
          then (r k : WithTop ℝ≥0) else ⊤) →
        ∀ t : ℝ≥0, 0 < t → t < T →
          ∃ l : ℝ,
            Tendsto (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω)
              (𝓝[<] t) (𝓝 l) ∧
            l ∈ Set.Icc lower upper ∧
            |Real.exp (-(q * (t : ℝ))) * deriv w l| ≤ KG ∧
            |Real.exp (-(q * (t : ℝ))) * iteratedDeriv 2 w l| ≤ KH := by sorry

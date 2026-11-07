-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_stopped_preexit_C2_jet_uniform_deterministic_bound
-- name    : AvramDividend.Classical.avram_wave7_18_original_stopped_preexit_C2_jet_uniform_deterministic_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:11:13.963266+00:00
-- url     : https://prove2.me/theorems/e67a4133-e024-458e-b1a9-4738dfc6f411
-- title:
--   Original bounded dense-grid stop controls the entire pre-exit C² jet with a deterministic bound
-- statement:
--   For the original controlled spectrally negative Lévy reserve and its right-continuous post-payment path, a dense-grid first exit from the positive closed band [lower,upper], stopped at deterministic B, gives exact original right-continuous-filtration stopping. At every strict pre-exit time s<T≤τ, the actual controlled post-payment reserve remains in the band. Hence one deterministic M≥0 uniformly bounds w(Z_s), its first ordinary derivative and its second ordinary derivative for every original path and pre-exit time. The original dense-stop right/left C² theorem supplies pre-exit band occupation; the original compact C² jet lemma supplies the finite bound. No integrability is claimed outside the bounded stopping region.

import Mathlib
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_dense_bounded_clock_right_left_uniform_C2
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_postpayment_C2_jet_uniformly_bounded_on_interior_band

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_18_original_stopped_preexit_C2_jet_uniform_deterministic_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (r : ℕ → ℝ≥0) (lower upper : ℝ)
    (hlower : 0 < lower) (hlu : lower ≤ upper)
    (hcap : ∀ y ∈ Set.Icc lower upper, ENNReal.ofReal y < C)
    (hdense : DenseRange r)
    (B : ℝ≥0) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ (ω : Ω) (T : ℝ≥0),
        (T : WithTop ℝ≥0) ≤
          min (⨅ k : ℕ,
            if x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨
                upper < x + X.X (r k) ω - rightLimit D (r k) ω
            then (r k : WithTop ℝ≥0) else ⊤) (B : WithTop ℝ≥0) →
        ∀ (s : ℝ≥0), s < T →
          |w (x + X.X s ω - rightLimit D s ω)| ≤ M ∧
          |deriv w (x + X.X s ω - rightLimit D s ω)| ≤ M ∧
          |deriv (deriv w) (x + X.X s ω - rightLimit D s ω)| ≤ M := by sorry

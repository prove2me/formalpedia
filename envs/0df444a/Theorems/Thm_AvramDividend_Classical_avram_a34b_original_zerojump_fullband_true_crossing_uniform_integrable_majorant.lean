-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a34b_original_zerojump_fullband_true_crossing_uniform_integrable_majorant
-- name    : AvramDividend.Classical.avram_a34b_original_zerojump_fullband_true_crossing_uniform_integrable_majorant
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T16:12:49.603585+00:00
-- url     : https://prove2.me/theorems/67cf5084-20f8-4f9f-92a7-502e1aa06112
-- title:
--   Actual finitecap Gaussian crossing positive errors admit one uniform integrable majorant over full reserve band
-- statement:
--   For the original zero-jump Gaussian Lévy X with random physical times s_m,t_m in [0,T], original bounded postpayment reserves y_m in [0,c], HJB candidate w continuous at all nonnegative states and zero on negative, produce a single nonnegative integrable random B dominating max(V(y_m+X(t_m)-X(s_m))-w(y_m),0) for ALL mesh indices m simultaneously. Follows from the previously Proved original same-X bounded horizon L1 increment majorant a28 and exact finitecap caplinear scalar crossing envelope a25. This supplies uniform integrability of the true zero-ruin-contact crossing source without artificial bounded w continuation.
-- source:
--   Same original ν=0 Gaussian physical stopped crossing spatial positive-part L1 envelope over actual reserve band [0,c].

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a34b_original_zerojump_fullband_true_crossing_uniform_integrable_majorant
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (T : ℝ≥0) (s t : ℕ → Ω → ℝ≥0)
    (hRange : ∀ᵐ ω ∂P, ∀ m,
      s m ω ∈ Set.Icc 0 T ∧ t m ω ∈ Set.Icc 0 T)
    (w : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hwcont : ContinuousOn w (Set.Ici 0))
    (hwneg : ∀ z : ℝ, z < 0 → w z = 0)
    (y : ℕ → Ω → ℝ)
    (hy : ∀ᵐ ω ∂P, ∀ m, y m ω ∈ Set.Icc 0 c) :
    ∃ B : Ω → ℝ, Integrable B P ∧
      (∀ᵐ ω ∂P, 0 ≤ B ω ∧ ∀ m,
        max ((if y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) ≤ c
           then w (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω))
           else w c + (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) - c)) -
           w (y m ω)) 0 ≤ B ω) := by sorry

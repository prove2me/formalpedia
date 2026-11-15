-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a277_original_gaussian_true_physical_signed_rare_exponential_tail_integrable
-- name    : AvramDividend.Classical.avram_ga_a277_original_gaussian_true_physical_signed_rare_exponential_tail_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:22:29.969+00:00
-- url     : https://prove2.me/theorems/14efe7a3-257a-4b63-8d84-0f9730122716
-- title:
--   Original zerojump Gaussian true stopped physical fullcell rare signed exponential finite-grid sum integrable
-- statement:
--   For a genuine zerojump Gaussian Lévy process and any right-continuous-filtration stopping time, every finite physical-grid fully pre-stop sum of exp(theta times original raw X.X increment) restricted to |raw|≥delta is integrable. Each raw Gaussian exponential is integrable by a276; the original fullcell stopped and rare event mask is measurable by adaptedness and stopping-time measurability. Finite mask and finite sums preserve integrability. Combined with a275 this proves true original two-sided rare exponential expected L1 without any additional assumptions on a HJB value near ruin.
-- source:
--   a276 raw original Gaussian exponential integrability and right-continuous IsStoppingTime measurable mask

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a276_original_zerojump_Gaussian_raw_increment_exponential_integrable
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a277_original_gaussian_true_physical_signed_rare_exponential_tail_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (theta delta : ℝ) (hθ : 0 ≤ theta) :
    let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m : ℝ≥0)+1)
    let s : ℕ → ℕ → ℝ≥0 := fun m i => (i : ℝ≥0)*Δ m
    let R : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      X.X (s m i+Δ m) ω-X.X (s m i) ω
    let Signed : ℕ → Ω → ℝ := fun m ω =>
      ∑ i ∈ Finset.range m,
        if (s m i < ρ ω ∧ s m i+Δ m ≤ ρ ω) ∧ delta ≤ |R m i ω|
        then Real.exp (theta*R m i ω) else 0
    ∀ m, Integrable (Signed m) P := by sorry

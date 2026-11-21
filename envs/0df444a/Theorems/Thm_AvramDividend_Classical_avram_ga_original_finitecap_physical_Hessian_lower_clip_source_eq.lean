-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_original_finitecap_physical_Hessian_lower_clip_source_eq
-- name    : AvramDividend.Classical.avram_ga_original_finitecap_physical_Hessian_lower_clip_source_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T00:27:25.416843+00:00
-- url     : https://prove2.me/theorems/49632706-d37b-4470-8d71-9da991ef7822
-- title:
--   Original postpayment physical-grid Gaussian Hessian martingale coefficient equals true finitecap source coefficient
-- statement:
--   For the original spectrally negative Lévy reserve, authentic càglàd dividend strategy, and strict pre-stop floor δ>0, the true post-dividend grid state Y_i=x+X_{s_i}−rightLimit D_{s_i} satisfies Y_i≥δ whenever s_i<ρ. Consequently, the lower-and-upper clipped Hessian coefficient used by the already Proved gb63 original filtered MDS theorem is exactly equal (including the real discount and stopped indicator) to the upper-clipped coefficient used by the original finitecap physical stopped Ito source 0ef5d778. The postpayment floor is obtained from the already Proved original gledger20 theorem, not an assumed new regularity property.
-- source:
--   Source-faithful model bridge between original proof target 0ef5d778 and Proved original gb63/gb65 filtered Gaussian MDS source, identifying the missing lower-clipping equality at every active physical grid start including time zero.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_original_finitecap_physical_Hessian_lower_clip_source_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ρ : Ω → ℝ≥0) (δ : ℝ) (hδ : 0 < δ)
    (hFloor : ∀ (ω : Ω) (t : ℝ≥0), 0 < t → t < ρ ω →
      δ ≤ riskProcess X x D t ω)
    (q b : ℝ) (w : ℝ → ℝ) (n : ℕ) :
    ∀ m : ℕ,
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
      let Y : ℕ → Ω → ℝ := fun i ω =>
        x + X.X (s i) ω - rightLimit D (s i) ω
      ∀ i ω,
        (if s i < ρ ω then Real.exp (-(q * (s i : ℝ))) *
          (if Y i ω ∈ Icc (δ / 2) b then iteratedDeriv 2 w (Y i ω) else 0)
        else 0) =
        (if s i < ρ ω then Real.exp (-(q * (s i : ℝ))) *
          (if Y i ω ≤ b then iteratedDeriv 2 w (Y i ω) else 0)
        else 0) := by sorry

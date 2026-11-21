-- Prove2me | Theorems.Thm_AvramDividend_Classical_original_purejump_esscher_Bernstein_exponent
-- name    : AvramDividend.Classical.original_purejump_esscher_Bernstein_exponent
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T22:56:56.8041+00:00
-- url     : https://prove2.me/theorems/1e2e9af0-0c07-4690-92f4-b51969e9dd33
-- title:
--   Exact original pure-jump Esscher-shifted Bernstein exponent at the positive Cramér root
-- statement:
--   For the original standing spectrally negative purejump Lévy process and any strictly positive root Φ of its original Laplace exponent ψ, the exact shifted function ψ(Φ+s)/(Φ+s) equals the Bernstein jump-tail integral ∫₀∞ exp(−Φt)(1−exp(−st))ν((−∞,−t))dt for s≥0. The original compensation cutoff and large negative-mark drift cancel by the true root identity. This is the substantive original-to-potential analytic bridge for pure-jump unbounded-variation zero-scale renewal existence, with no abstract replacement Lévy measure and no unproved scale-function existence assumption.
-- source:
--   Exact original ψ/θ negative-tail identity 0fded7ba and original finite Esscher tail cancellation b3fe2176 publication; source target 2fa29eaf.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.original_purejump_esscher_Bernstein_exponent
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hσ : X.σ = 0) (Φ : ℝ) (hΦ : 0 < Φ)
    (hRoot : X.ψ Φ = 0) (s : ℝ) (hs : 0 ≤ s) :
    X.ψ (Φ + s) / (Φ + s) =
      (∫ t in Ioi (0 : ℝ),
        Real.exp (-(Φ * t)) * (1 - Real.exp (-(s * t))) *
          (X.ν (Iio (-t))).toReal) := by sorry

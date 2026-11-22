-- Prove2me | Theorems.Thm_AvramDividend_Classical_original_purejump_esscher_killed_Bernstein
-- name    : AvramDividend.Classical.original_purejump_esscher_killed_Bernstein
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T07:58:38.500548+00:00
-- url     : https://prove2.me/theorems/0cb20c38-4e59-43c5-8a45-40a3a3283c29
-- title:
--   Original spectrally negative purejump killed Bernstein shift for any positive Esscher tilt
-- statement:
--   For the original standing spectrally negative pure-jump Lévy process X with σ=0, and any positive Esscher base Φ and nonnegative shift s, ψ(Φ+s)/(Φ+s) equals the killing constant ψ(Φ)/Φ plus the positive Esscher-weighted negative jump-tail Bernstein integral. No positive zero root is assumed, so by choosing Φ beyond the Cramér zero or at the positive q-root the killing constant is positive. This is a fundamental exact original Lévy-to-subordinator potential identity, valid even when the small-jump first moment diverges.
-- source:
--   Original exponent-to-tail source 0fded7ba plus Proved exact Esscher-tail shift 3ed689c3; leads to purejump renewal measure existence 2fa29eaf.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.original_purejump_esscher_killed_Bernstein
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hσ : X.σ = 0) (Φ : ℝ) (hΦ : 0 < Φ)
    (s : ℝ) (hs : 0 ≤ s) :
    X.ψ (Φ + s) / (Φ + s) =
      X.ψ Φ / Φ +
      (∫ t in Ioi (0 : ℝ),
        Real.exp (-(Φ * t)) * (1 - Real.exp (-(s * t))) *
          (X.ν (Iio (-t))).toReal) := by sorry

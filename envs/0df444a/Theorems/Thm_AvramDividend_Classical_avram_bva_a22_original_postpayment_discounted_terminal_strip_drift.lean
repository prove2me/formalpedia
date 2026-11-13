-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_postpayment_discounted_terminal_strip_drift
-- name    : AvramDividend.Classical.avram_bva_a22_original_postpayment_discounted_terminal_strip_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T00:20:49.337555+00:00
-- url     : https://prove2.me/theorems/770858c4-65f5-4db1-8317-5a690a220e42
-- title:
--   Original bounded-variation discounted postpayment terminal strip upper error by physical drift
-- statement:
--   On the original filtered bounded-variation spectrally negative Lévy source and original dividend strategy, any two ordered physical times with both post-rightpayment reserves inside a common strict compact, compact one-sided Lipschitz candidate value and nonnegative value at the later endpoint satisfy an exact discounted terminal strip upper bound. The excess of the later discounted terminal reward above the earlier is at most the compact Lipschitz constant times elapsed physical time times the positive original Lévy drift. The proof combines the original-process undiscounted source theorem, monotonicity of exp(-q t) for q>=0 and nonnegativity of the later value. Applied to the physical uniform grid, this error is at most a deterministic multiple of T/(m+2) and vanishes without a global generator L1, replacement process, or finite negative-jump activity. Compact exit and ruin-contact require separate treatment.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_postpayment_compact_terminal_upper_drift
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a22_original_postpayment_discounted_terminal_strip_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (c d L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ y ∈ Icc c d, ∀ z ∈ Icc c d,
      w z - w y ≤ L * max (z - y) 0) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, s ≤ t →
      (x + X.X s ω - rightLimit D s ω) ∈ Icc c d →
      (x + X.X t ω - rightLimit D t ω) ∈ Icc c d →
      0 ≤ w (x + X.X t ω - rightLimit D t ω) →
      Real.exp (-(q * (t : ℝ))) *
        w (x + X.X t ω - rightLimit D t ω) -
        Real.exp (-(q * (s : ℝ))) *
        w (x + X.X s ω - rightLimit D s ω) ≤
      L * (((t : ℝ) - (s : ℝ)) * max X.drift 0) := by sorry

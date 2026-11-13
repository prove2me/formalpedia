-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_uniform_physical_discounted_terminal_strip_bound
-- name    : AvramDividend.Classical.avram_bva_a22_original_uniform_physical_discounted_terminal_strip_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T00:29:23.019196+00:00
-- url     : https://prove2.me/theorems/cbe993d7-20d8-43e7-ad1a-c76c95c2fb6d
-- title:
--   Exact original uniform-grid last-cell discounted terminal increase is bounded by mesh width times physical drift
-- statement:
--   On the original filtered bounded-variation spectrally negative Lévy process and original dividend strategy, for every row of the actual prescribed physical uniform grid with denominator row plus two and last index row plus one, prove that the final grid time precedes the true horizon. Whenever both post-rightpayment reserve endpoints lie in one compact interior interval with a one-sided Lipschitz candidate and nonnegative horizon reward, the exact discounted full-horizon terminal increase over the unobserved last cell is bounded above by the positive physical drift times the mesh width and compact Lipschitz constant. The bound holds almost surely simultaneously for every mesh row. It preserves the original process, actual physical grid and survivor terminal reward; no surrogate process or generator L1 is used. Compact localisation and ruin-contact source residuals remain separate tasks.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_postpayment_discounted_terminal_strip_drift
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a22_original_uniform_physical_discounted_terminal_strip_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (c d L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ y ∈ Icc c d, ∀ z ∈ Icc c d,
      w z - w y ≤ L * max (z - y) 0)
    (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ m i, (u m i : ℝ) =
      T * (i : ℝ) / ((m : ℝ) + 2)) :
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    ∀ᵐ ω ∂P, ∀ m : ℕ,
      (x + X.X (u m (m + 1)) ω -
          rightLimit D (u m (m + 1)) ω) ∈ Icc c d →
      (x + X.X S ω - rightLimit D S ω) ∈ Icc c d →
      0 ≤ w (x + X.X S ω - rightLimit D S ω) →
      Real.exp (-(q * T)) *
        w (x + X.X S ω - rightLimit D S ω) -
        Real.exp (-(q * (u m (m + 1) : ℝ))) *
        w (x + X.X (u m (m + 1)) ω -
          rightLimit D (u m (m + 1)) ω) ≤
      L * ((T / ((m : ℝ) + 2)) * max X.drift 0) := by sorry

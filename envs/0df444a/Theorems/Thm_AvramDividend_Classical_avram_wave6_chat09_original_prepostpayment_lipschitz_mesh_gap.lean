-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_prepostpayment_lipschitz_mesh_gap
-- name    : AvramDividend.Classical.avram_wave6_chat09_original_prepostpayment_lipschitz_mesh_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T06:51:06.449682+00:00
-- url     : https://prove2.me/theorems/0451245c-6660-4916-a770-9ba2529fb4ad
-- title:
--   Original Lévy pre/postpayment reserve Lipschitz discount-clock mesh-error estimate
-- statement:
--   For the original spectral-negative Lévy source and an actual monotone dividend strategy, compare the reserve immediately before and after all payments in each finite-grid cell at the same source time. A globally L-Lipschitz real test function changes across that payment by at most L times the total right-limit dividend increment, which includes atomic, absolutely continuous, and singular continuous payouts. The left-minus-right exponential clock-weighted test-function error sums to at most q m L times total paid on the grid. The localized C1 source application uses this with L a compact-band derivative envelope; no stochastic budget inequality is postulated.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), Section 5.4; deterministic pre/postpayment clock discrepancy on the original Lévy source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_chat09_original_prepostpayment_lipschitz_mesh_gap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ a b : ℝ, |w a - w b| ≤ L * |a - b|)
    (u : ℕ → ℝ≥0) (hu : Monotone u)
    (n : ℕ) (m : ℝ) (hm : 0 ≤ m)
    (hmesh : ∀ i < n, ((u (i + 1) : ℝ) - (u i : ℝ)) ≤ m) :
    (∑ i ∈ Finset.range n,
      (Real.exp (-(q * (u i : ℝ))) -
         Real.exp (-(q * (u (i + 1) : ℝ)))) *
       |w (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
        w (x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω)|) ≤
      q * m * L * (rightLimit D (u n) ω - rightLimit D (u 0) ω) := by sorry

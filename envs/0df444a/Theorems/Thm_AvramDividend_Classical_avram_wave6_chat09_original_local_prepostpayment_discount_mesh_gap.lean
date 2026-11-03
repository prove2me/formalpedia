-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_local_prepostpayment_discount_mesh_gap
-- name    : AvramDividend.Classical.avram_wave6_chat09_original_local_prepostpayment_discount_mesh_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T07:00:58.688379+00:00
-- url     : https://prove2.me/theorems/3c4bf891-c4ce-44f0-a690-00da04c217dd
-- title:
--   Local compact-band original-source pre/postpayment Lipschitz discount-grid error
-- statement:
--   On every original spectrally negative Lévy sample path with its actual dividend strategy, assume the prepayment and postpayment reserve at each same source grid time are in a prescribed closed real interval, and w has a local L-Lipschitz bound on that interval. Then the sum of left-minus-right discount factors multiplied by the absolute value of the payment-induced w change is bounded by q m L times the complete cumulative right-limit dividend increment. The exact source time cancels in each reserve difference; no replacement of continuous or singular-continuous payments by jumps occurs. This is the compact-band pathwise clock-gap bridge needed for bounded-variation C1 stochastic verification, and imports the already-Proved pure-dividend mesh estimate.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), Section 5.4, original Lévy compensated-grid C1 verification, compact-reserve-strip Stieltjes discount timing.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_dividend_rightlimit_discount_mesh_gap

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_chat09_original_local_prepostpayment_discount_mesh_gap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (a b : ℝ) (hLip : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, |w s - w t| ≤ L * |s - t|)
    (u : ℕ → ℝ≥0) (hu : Monotone u) (n : ℕ) (m : ℝ) (hm : 0 ≤ m)
    (hmesh : ∀ i < n, ((u (i + 1) : ℝ) - (u i : ℝ)) ≤ m)
    (hPre : ∀ i < n, x + X.X (u (i + 1)) ω - rightLimit D (u i) ω ∈ Icc a b)
    (hPost : ∀ i < n, x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω ∈ Icc a b) :
    (∑ i ∈ Finset.range n,
      (Real.exp (-(q * (u i : ℝ))) -
         Real.exp (-(q * (u (i + 1) : ℝ)))) *
       |w (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
        w (x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω)|) ≤
      q * m * L * (rightLimit D (u n) ω - rightLimit D (u 0) ω) := by sorry

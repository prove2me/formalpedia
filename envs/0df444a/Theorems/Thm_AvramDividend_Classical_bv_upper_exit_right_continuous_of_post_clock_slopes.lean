-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_upper_exit_right_continuous_of_post_clock_slopes
-- name    : AvramDividend.Classical.bv_upper_exit_right_continuous_of_post_clock_slopes
-- status  : Proved
-- author  : @RSoulat
-- created : 2026-11-22T15:14:57.009786+00:00
-- url     : https://prove2.me/theorems/52ffd941-cae8-49a6-a601-d99f175da589
-- title:
--   Right-continuity of strict upward passage at a bounded-variation boundary contact
-- statement:
--   Let $X$ be a spectrally negative Lévy process of bounded variation with physical drift $d$. Suppose its Laplace exponent satisfies $\psi(\phi)=q$ for some $\phi>0$ and $q>0$. Let $\tau$ assign a finite nonnegative time to each sample point, and let $(\delta_n)_{n\ge0}$ be a positive mesh with $\delta_n\le 2\delta_{n+1}$. Assume that for every $N$, each $t$ with $0<t<\delta_N$ belongs to some $[\delta_{n+1},\delta_n]$ with $n\ge N$. Suppose that almost surely
--
--   $$
--   \lim_{n\to\infty}
--   \frac{d\,\delta_n-(X_{\tau+\delta_n}-X_\tau)}{\delta_n}=0.
--   $$
--
--   Write $T_b=\inf\{t\ge0:X_t>b\}$, where the infimum of the empty set is $+\infty$. Then, for almost every path on which $X_s\le X_\tau$ for every $s<\tau$, the contact level $a=X_\tau$ satisfies
--
--   $$
--   T_a=\tau,\qquad \lim_{b\downarrow a}T_b=\tau.
--   $$
--
--   This identifies the strict passage clock at contact and gives its stability as the barrier is raised slightly.
-- source:
--   Corollary of AvramDividend.Classical.p2m81_bv_post_clock_positive_germ_of_dyadic_zero_no_standing_public (https://prove2.me/theorems/728b880d-e3d2-468b-8bb1-72e2ab895082), using the strict upper-exit clock in Definitions.Def_AvramDividend_Classical_TwoSidedExit.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open AvramDividend.Classical MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

set_option autoImplicit false

theorem AvramDividend.Classical.bv_upper_exit_right_continuous_of_post_clock_slopes {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (hBV : X.BoundedVariation) (τ : Ω → ℝ≥0) (δ : ℕ → ℝ≥0)
    (hδpos : ∀ n, 0 < δ n)
    (hRatio : ∀ n, (δ n : ℝ) ≤ 2 * (δ (n + 1) : ℝ))
    (hCover : ∀ (N : ℕ) (t : ℝ≥0), 0 < t → t < δ N →
      ∃ n : ℕ, N ≤ n ∧ δ (n + 1) ≤ t ∧ t ≤ δ n)
    (hSlope : ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ =>
        (X.drift * (δ n : ℝ) - (X.X (τ ω + δ n) ω - X.X (τ ω) ω)) /
          (δ n : ℝ)) atTop (𝓝 (0 : ℝ))) :
    ∀ᵐ ω ∂P,
      (∀ s : ℝ≥0, s < τ ω → X.X s ω ≤ X.X (τ ω) ω) →
      twoSidedExitUpTime X (X.X (τ ω) ω) ω = (τ ω : ℝ≥0∞) ∧
      Tendsto (fun b : ℝ => twoSidedExitUpTime X b ω)
        (𝓝[Ici (X.X (τ ω) ω)] (X.X (τ ω) ω)) (𝓝 (τ ω : ℝ≥0∞)) := by sorry

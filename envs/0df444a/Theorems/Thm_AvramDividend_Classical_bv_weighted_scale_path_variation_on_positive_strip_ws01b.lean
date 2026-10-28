-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_weighted_scale_path_variation_on_positive_strip_ws01b
-- name    : AvramDividend.Classical.bv_weighted_scale_path_variation_on_positive_strip_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T20:45:46.824742+00:00
-- url     : https://prove2.me/theorems/7a818ab7-1fa7-4443-a20e-7554babf863a
-- title:
--   Discounted BV scale payoff variation on positive reserve strips
-- statement:
--   For an actual bounded-variation spectrally negative Lévy path stopped inside a strictly positive reserve strip, the q-scale values multiplied by any decreasing discount weights in [0,1] have total finite-partition variation at most the physical path-variation budget multiplied by a local Lipschitz constant, plus W(a) times the total discount decrease. This pathwise inequality holds on a common probability-one event for every partition and every discount schedule, including exponential discounts. It supplies the discounted finite-variation estimate for the boundary-localised jump Dynkin argument, without needing Lévy–Itô or global smoothness of W at zero.
-- source:
--   Canonically Proved bv_scale_path_variation_on_positive_strip_ws01b, positivity and monotonicity clauses of IsScaleFunction, and the algebraic product-variation inequality for decreasing weights.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_bv_scale_path_variation_on_positive_strip_ws01b

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_weighted_scale_path_variation_on_positive_strip_ws01b
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (ε a x : ℝ) (hε : 0 < ε) (hεa : ε ≤ a) :
    ∃ K : ℝ≥0, ∀ᵐ ω ∂P, ∀ (u : ℕ → ℝ≥0),
      Monotone u → ∀ (n : ℕ),
      (∀ i : ℕ, i ≤ n → x + X.X (u i) ω ∈ Icc ε a) →
      ∀ (d : ℕ → ℝ), Antitone d →
      (∀ i, 0 ≤ d i) → (∀ i, d i ≤ 1) →
      (∑ i ∈ Finset.range n,
        |d (i + 1) * W (x + X.X (u (i + 1)) ω) -
           d i * W (x + X.X (u i) ω)|) ≤
        (K : ℝ) *
          (2 * X.drift * ((u n : ℝ) - (u 0 : ℝ)) -
            (X.X (u n) ω - X.X (u 0) ω)) +
          W a * (d 0 - d n) := by sorry

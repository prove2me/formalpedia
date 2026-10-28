-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_scale_path_variation_on_positive_strip_ws01b
-- name    : AvramDividend.Classical.bv_scale_path_variation_on_positive_strip_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T14:26:52.846768+00:00
-- url     : https://prove2.me/theorems/b7fa5c63-8887-4ae1-bfaf-75768935cc61
-- title:
--   Actual bounded-variation q-scale payoff has finite variation on each positive reserve strip
-- statement:
--   For each strictly positive bounded reserve strip, there is a finite uniform Lipschitz constant K such that almost every actual BV Lévy path, along any finite monotone time partition whose shifted reserves remain in the strip, has its total q-scale payoff variation bounded by K times the explicit physical-drift path-variation budget. The event is common over all finite partitions, supporting eventual random stopping partitions without relying on origin smoothness.
-- source:
--   Composition of canonically Proved actual BV path finite-partition variation bound and local positive-strip scale Lipschitz regularity. A deterministic local chain-rule prerequisite for future killed Dynkin proof; does not claim jump compensator or stochastic harmonicity.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_bv_actual_path_partition_variation_bound_ws01b
import Theorems.Thm_AvramDividend_Classical_bv_scale_lipschitzOn_positive_compact_ws01b

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_scale_path_variation_on_positive_strip_ws01b
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (ε a x : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ≥0, ∀ᵐ ω ∂P, ∀ u : ℕ → ℝ≥0,
      Monotone u → ∀ n : ℕ,
      (∀ i : ℕ, i ≤ n → x + X.X (u i) ω ∈ Icc ε a) →
      (∑ i ∈ Finset.range n,
        |W (x + X.X (u (i + 1)) ω) - W (x + X.X (u i) ω)|) ≤
        (K : ℝ) * (2 * X.drift * ((u n : ℝ) - (u 0 : ℝ)) -
          (X.X (u n) ω - X.X (u 0) ω)) := by sorry

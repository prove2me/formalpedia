-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_discounted_J_commutator_total_variation_budget
-- name    : AvramDividend.Classical.avram_p3_f2_original_discounted_J_commutator_total_variation_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T23:09:28.60852+00:00
-- url     : https://prove2.me/theorems/2d074f42-b39d-4a33-a96f-7a2d62406338
-- title:
--   Original physical negative-J total variation bounds the full discounted mixed Y-J C1 commutator
-- statement:
--   For almost every path of the actual bounded-variation spectrally negative Levy process, any monotone finite physical clock grid and source reserve/dividend process, a source cellwise mixed Y/J commutator estimate is summable with actual exponential discount. The discounted accumulated commutator is bounded by epsilon times the genuine raw negative-jump mass J(u n)-J(u 0), using the Proved source-exact J grid telescope.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_raw_negative_J_grid_total_variation_exact
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_f2_original_discounted_J_commutator_total_variation_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) :
    ∀ᵐ ω ∂P,
      ∀ (u : ℕ → ℝ≥0) (n : ℕ),
        let J : ℝ≥0 → ℝ := fun t =>
          ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
        let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
        let z : ℕ → ℝ := fun i =>
          x + X.X (u i) ω - rightLimit D (u i) ω
        let c : ℕ → ℝ := fun i => Y (u (i + 1)) - Y (u i)
        let j : ℕ → ℝ := fun i => J (u (i + 1)) - J (u i)
        (∀ i, i < n → u i ≤ u (i + 1)) →
        ∀ ε : ℝ, 0 ≤ ε →
        (∀ i, i < n →
          |w (z i + c i - j i) - w (z i + c i) -
            w (z i - j i) + w (z i)| ≤ ε * |j i|) →
        ∀ q : ℝ, 0 ≤ q →
          |∑ i ∈ Finset.range n,
            Real.exp (-q * (u i : ℝ)) *
              (w (z i + c i - j i) - w (z i + c i) -
                w (z i - j i) + w (z i))| ≤
          ε * (J (u n) - J (u 0)) := by sorry

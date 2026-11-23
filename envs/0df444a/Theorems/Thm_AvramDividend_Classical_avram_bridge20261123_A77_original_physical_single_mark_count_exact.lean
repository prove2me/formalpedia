-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bridge20261123_A77_original_physical_single_mark_count_exact
-- name    : AvramDividend.Classical.avram_bridge20261123_A77_original_physical_single_mark_count_exact
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T16:44:13.724628+00:00
-- url     : https://prove2.me/theorems/8b9b4431-7300-46af-acc0-25cfac1031d0
-- title:
--   Original physical Borel simple negative-mark count equals its exactly supported pathwise sum
-- statement:
--   For the same original spectrally negative Levy process, a physical finite negative-jump support and a finite Borel partition of a nonpositive SimpleFunc, prove the weighted physical jump-count is measurable and nonpositive almost surely and equals the actual pathwise finite-mark sum. Reuse the proved original Borel count equals marked-support filter card lemma and physical Borel count filtration measurability.
-- source:
--   Original A77 single-fibre target 6c3848; proved a27 count-to-filter card 11e24cb0; proved a28 count measurability 60ce8fc6; source strict jump negativity 2ba2b75a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_bridge20261123_A77_original_physical_single_mark_count_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (J : Ω → ℝ)
    (hSupport :
      ∀ᵐ ω ∂P, ∃ S : Finset ℝ≥0,
        (∀ u, u ∈ S ↔ 0 < u ∧ u ≤ t ∧
          X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u ≠ 0) ∧
        J ω = ∑ u ∈ S,
          (X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u))
    (g : SimpleFunc ℝ ℝ) (hg : ∀ y, g y ≤ 0)
    (K : ℕ) (B : ℕ → Set ℝ) (c : ℕ → ℝ)
    (hB : ∀ i ∈ Finset.range K,
      MeasurableSet (B i) ∧ B i ⊆ Iio (0 : ℝ))
    (hDisj : ∀ i ∈ Finset.range K,
      ∀ j ∈ Finset.range K, i ≠ j → Disjoint (B i) (B j))
    (hTransfer : ∀ w : ℝ → ℝ,
      (∑ i ∈ Finset.range K, w (c i)) = ∑ y ∈ g.range, w y)
    (hFibre : ∀ i ∈ Finset.range K,
      B i = Iio (0 : ℝ) ∩ g ⁻¹' {c i}) :
    let f : Ω → ℝ := fun ω =>
      ∑ i ∈ Finset.range K, c i *
        (((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 t ×ˢ B i)).toReal
    Measurable f ∧
      (∀ᵐ ω ∂P, f ω ≤ 0) ∧
      (∀ᵐ ω ∂P, ∀ S : Finset ℝ≥0,
        (∀ u, u ∈ S ↔ 0 < u ∧ u ≤ t ∧
          X.X u ω -
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) u ≠ 0) →
        f ω = ∑ u ∈ S,
          g (X.X u ω -
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) u)) := by sorry

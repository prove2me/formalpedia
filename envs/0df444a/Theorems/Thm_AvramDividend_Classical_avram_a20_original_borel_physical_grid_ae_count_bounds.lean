-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_original_borel_physical_grid_ae_count_bounds
-- name    : AvramDividend.Classical.avram_a20_original_borel_physical_grid_ae_count_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T17:38:48.521205+00:00
-- url     : https://prove2.me/theorems/2cfac3a4-d363-4780-83c1-630389abd941
-- title:
--   Original finite-activity Borel physical grid marked-pair counts are almost surely bounded and eventually exact
-- statement:
--   For the original finite negative-activity spectrally negative Lévy process and any Borel negative jump mark subset B, the exact original physical marked past–future finite-grid count sum is bounded almost surely by the literal chronological Set.ncard of pairs at every grid size and equals that physical pair count at every sufficiently fine uniform mesh, almost surely. This derives the two needed a.e. hypotheses by combining the independently Proved a.e. finiteness of original Borel marked jump times and the finite-source pathwise uniform-grid count bridge, with no assumed Poisson law, factorial count moment or sample-space substitution.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a20_original_borel_physical_grid_ae_count_bounds
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (hT : 0 < T)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hNeg : B ⊆ Iio (0 : ℝ)) :
    let S : Ω → Set ℝ≥0 := fun ω => {u : ℝ≥0 |
      0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ B}
    let K : Ω → ℕ := fun ω => ((S ω ×ˢ S ω) ∩
      {p : ℝ≥0 × ℝ≥0 | p.1 < p.2}).ncard
    let N : ℝ≥0 → ℝ≥0 → Ω → ℝ≥0∞ := fun a b ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc a b ×ˢ B)
    let A : ℕ → Ω → ℝ≥0∞ := fun k ω =>
      ∑ i : Fin k,
        N 0 (((i.val : ℝ≥0) * T) / (k : ℝ≥0)) ω *
        N (((i.val : ℝ≥0) * T) / (k : ℝ≥0))
          ((((i.val + 1 : ℕ) : ℝ≥0) * T) / (k : ℝ≥0)) ω
    (∀ᵐ ω ∂P, ∀ k, A k ω ≤ (K ω : ℝ≥0∞)) ∧
    (∀ᵐ ω ∂P, ∀ᶠ k in atTop, A k ω = (K ω : ℝ≥0∞)) := by sorry

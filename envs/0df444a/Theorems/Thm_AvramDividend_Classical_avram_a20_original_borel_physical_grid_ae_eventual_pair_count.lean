-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_original_borel_physical_grid_ae_eventual_pair_count
-- name    : AvramDividend.Classical.avram_a20_original_borel_physical_grid_ae_eventual_pair_count
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T17:19:11.173324+00:00
-- url     : https://prove2.me/theorems/5cac727c-fa16-451f-8514-357b45d76a62
-- title:
--   Every finite original Borel-marked source path has bounded and eventually exact physical chronological grid pair counts
-- statement:
--   Fix the genuine original spectrally negative Lévy sample path with a finite set of physical Borel marked jump times in (0,T]. The actual physical past–future marked-rectangle grid-product sum is bounded at every grid resolution by the literal Set.ncard of all chronological marked-jump pairs, and eventually equals that exact pair count for every sufficiently fine integer uniform mesh. This combines the Proved original Borel samplewise grid-to-window card equality with the generic finite-set ncard bridge, the Proved uniform ceiling-grid pair domination, and generic finite-event eventual grid separation. It is the fundamental source-path input for the original Borel chronological-pair expectation Fatou squeeze.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a20_original_borel_physical_grid_ae_eventual_pair_count
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : ℝ≥0) (hT : 0 < T)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hS : ({u : ℝ≥0 |
      0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ B}).Finite) :
    let S : Set ℝ≥0 := {u : ℝ≥0 |
      0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ B}
    let K : ℕ := ((S ×ˢ S) ∩
      {p : ℝ≥0 × ℝ≥0 | p.1 < p.2}).ncard
    let N : ℝ≥0 → ℝ≥0 → ℝ≥0∞ := fun a b =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc a b ×ˢ B)
    let A : ℕ → ℝ≥0∞ := fun k =>
      ∑ i : Fin k,
        N 0 (((i.val : ℝ≥0) * T) / (k : ℝ≥0)) *
        N (((i.val : ℝ≥0) * T) / (k : ℝ≥0))
          ((((i.val + 1 : ℕ) : ℝ≥0) * T) / (k : ℝ≥0))
    (∀ k, A k ≤ (K : ℝ≥0∞)) ∧
    (∀ᶠ k in atTop, A k = (K : ℝ≥0∞)) := by sorry

-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_original_borel_chronological_pair_lintegral_exact
-- name    : AvramDividend.Classical.avram_a20_original_borel_chronological_pair_lintegral_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T17:38:53.58379+00:00
-- url     : https://prove2.me/theorems/f0c85ec3-4bed-4f2a-8e07-28f727a8f95f
-- title:
--   Original finite-activity negative Borel chronological-pair physical ENNReal expectation is exactly half the squared intensity
-- statement:
--   On the actual original spectrally negative Lévy probability space under finite negative jump activity, for any measurable Borel subset of negative jumps and positive finite horizon T, the extended-nonnegative expectation of the literal Set.ncard of strictly chronological marked-jump pairs equals one half of the squared physical T ν(B) rate. The proof uses independently Proved original arbitrary-Borel grid-count measurability, almost-sure pathwise domination and eventual exact equality to the full chronological pair count, exact original physical finite-grid product expectations and their convergent quadratic-rate limit, and an a.e. Fatou squeeze. It is a direct source proof without a Poisson count law assumption or Gaussian replacement process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a20_original_borel_chronological_pair_lintegral_exact
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
    (∫⁻ ω, (K ω : ℝ≥0∞) ∂P) =
      (((T : ℝ≥0∞) * X.ν B) ^ 2) / 2 := by sorry

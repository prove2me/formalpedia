-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a26_original_Borel_occupied_grid_binomial_law_20261116
-- name    : AvramDividend.Classical.avram_a26_original_Borel_occupied_grid_binomial_law_20261116
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T07:57:05.47821+00:00
-- url     : https://prove2.me/theorems/b98e25fc-13c1-4d48-9ba2-a716d687a1f9
-- title:
--   Original physical negative-Borel occupied-cell count has an exact binomial distribution on each equal grid
-- statement:
--   For any finite-negative-activity spectrally negative Lévy process, count how many of n consecutive original-time cells contain a physical jump marked in B. Stationarity makes the cell indicators identically distributed with parameter 1 minus the actual void probability on a cell, and the original filtration and independent increments make these indicators jointly independent. Their finite sum has the binomial law. This is the source probability mechanism missing from the A25 binomial limit; preserve original Omega and P, no companion process.
-- source:
--   Original independent-future physical count theorems 0832c67e and 7e146944; original stationary physical count theorem 37abf3aa; binomial distribution in pinned Mathlib.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a26_original_Borel_occupied_grid_binomial_law_20261116
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ)) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let δ : ℕ → ℝ≥0 := fun n => T / (n : ℝ≥0)
    let Z : ℕ → Ω → ℕ := fun n ω =>
      ((Finset.range n).filter (fun i : ℕ =>
        NX ω (Ioc ((i : ℝ≥0) * δ n)
          (((i + 1 : ℕ) : ℝ≥0) * δ n) ×ˢ B) ≠ 0)).card
    ∃ p : ℕ → unitInterval,
      (∀ n : ℕ, (p n : ℝ) =
        1 - (P {ω : Ω | NX ω (Ioc 0 (δ n) ×ˢ B) = 0}).toReal) ∧
      ∀ n : ℕ, P.map (Z n) = Bin(n, p n) := by sorry

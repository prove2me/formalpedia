-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_f_original_physical_grid_quadratic_energy_upper
-- name    : AvramDividend.Classical.avram_p4_s3_interval_f_original_physical_grid_quadratic_energy_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T14:12:23.492081+00:00
-- url     : https://prove2.me/theorems/5f827d8e-9444-464e-a740-e47046ae8244
-- title:
--   Original physical predictable finite-grid compensated kernel has explicit bounded-coefficient quadratic energy
-- statement:
--   On the same physical spectrally negative Lévy X, an actual finite grid of marked compensated jump counts with adapted L2 bounded weights has expected terminal square at most L² times the sum of source Lévy rates over grid cells. This follows from the Proved exact original physical grid isometry and the probability-measure bound on each weight. The genuine conditional count-square and predictable-prefix hypotheses are explicit; the estimate is a finite-band quadratic budget for subsequent small-jump localisation.
-- source:
--   Proved original source-exact physical grid isometry ccfd7ded-2cf1-4ea0-8b95-e7c2f95d4f16. Integrability follows from MemLp.integrable_sq at pinned Mathlib; original rate nonnegativity and integral monotonicity give the explicit energy bound.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_e_original_physical_grid_isometry_l2_integrability_auto
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_interval_f_original_physical_grid_quadratic_energy_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (cut : ℕ)
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (hTime : ∀ i, grid i ≤ T)
    (ε : ℝ) (hε : 0 < ε) (B : ℕ → Set ℝ)
    (hB : ∀ i, MeasurableSet (B i))
    (hBand : ∀ i, B i ⊆ Ioo (-1 : ℝ) (-ε))
    (hCut : ∀ i, B i ⊆ Iic (-(1 / ((cut : ℝ) + 1))))
    (hν : ∀ i, X.ν (B i) < ⊤)
    (N : ℕ → Ω → ℝ≥0∞)
    (hActual : ∀ i, N i = fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ B i))
    (r : ℕ → ℝ)
    (hRate : ∀ i, r i =
      (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)).toReal)
    (H D : ℕ → Ω → ℝ)
    (hD : ∀ i ω, D i ω = H i ω * ((N i ω).toReal - r i))
    (hH : ∀ i, StronglyMeasurable[𝓕 (grid i)] (H i))
    (hHL2 : ∀ i, MemLp (H i) 2 P)
    (L : ℝ) (hL : 0 ≤ L) (hBound : ∀ i ω, |H i ω| ≤ L)
    (hPrefix : ∀ i, StronglyMeasurable[𝓕 (grid i)]
      (fun ω => ∑ j ∈ Finset.range i, D j ω))
    (hSecond : ∀ i, P[(fun ω => ((N i ω).toReal - r i) ^ 2)
      | 𝓕 (grid i)] =ᵐ[P] (fun _ => r i))
    (n : ℕ) :
    (∫ ω, (∑ i ∈ Finset.range n, D i ω) ^ 2 ∂P) ≤
      (∑ i ∈ Finset.range n, r i) * L ^ 2 := by sorry

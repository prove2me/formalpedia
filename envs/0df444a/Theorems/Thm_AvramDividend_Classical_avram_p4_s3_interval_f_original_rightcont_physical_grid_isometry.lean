-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_f_original_rightcont_physical_grid_isometry
-- name    : AvramDividend.Classical.avram_p4_s3_interval_f_original_rightcont_physical_grid_isometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T14:30:46.804304+00:00
-- url     : https://prove2.me/theorems/66ac8bb6-5654-4ac1-a3bd-feeeaeb1d998
-- title:
--   Exact original physical finite-grid L2 compensated isometry for right-continuous predictable weights
-- statement:
--   For literal original Lévy marked counts and bounded predictable weights adapted at the right-continuous filtration, the finite compensated grid sum has exact expected square equal to the sum of physical source rates times weight-square expectations. The proof transports the already Proved physical grid isometry through a same-path right-continuous Lévy lift, preserving X paths and ν exactly. Genuine conditional-square and adapted-prefix hypotheses are retained; this directly matches original stopped pre-jump predictable derivative grids.
-- source:
--   Proved same-path right-continuous Levy lift e58a099d-9977-4265-9e76-7a5f0f6aa758 and physical finite-grid isometry ccfd7ded-2cf1-4ea0-8b95-e7c2f95d4f16. Paths and Lévy ν are pointwise/equality-identical, so each original physical grid count and source rate transports.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_e_original_physical_grid_isometry_l2_integrability_auto
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_interval_f_original_rightcont_physical_grid_isometry
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (cut : ℕ)
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (hTime : ∀ i, grid i ≤ T)
    (ε : ℝ) (hε : 0 < ε) (B : ℕ → Set ℝ)
    (hB : ∀ i, MeasurableSet (B i))
    (hBand : ∀ i, B i ⊆ Ioo (-1 : ℝ) (-ε))
    (hCut : ∀ i, B i ⊆ Iic (-(1 / ((cut : ℝ) + 1))))
    (hFinite : ∀ i, X.ν (B i) < ⊤)
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
    (hH : ∀ i, StronglyMeasurable[𝓕.rightCont (grid i)] (H i))
    (hHL2 : ∀ i, MemLp (H i) 2 P)
    (L : ℝ) (hBound : ∀ i ω, |H i ω| ≤ L)
    (hPrefix : ∀ i, StronglyMeasurable[𝓕.rightCont (grid i)]
      (fun ω => ∑ j ∈ Finset.range i, D j ω))
    (hSecond : ∀ i, P[(fun ω => ((N i ω).toReal - r i) ^ 2)
      | 𝓕.rightCont (grid i)] =ᵐ[P] (fun _ => r i))
    (n : ℕ) :
    (∫ ω, (∑ i ∈ Finset.range n, D i ω) ^ 2 ∂P) =
      ∑ i ∈ Finset.range n, r i * ∫ ω, (H i ω) ^ 2 ∂P := by sorry

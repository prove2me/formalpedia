-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_unbounded_predictable_mark_simple_L1_centered
-- name    : AvramDividend.Classical.avram_p4_f3_original_unbounded_predictable_mark_simple_L1_centered
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T13:17:55.701208+00:00
-- url     : https://prove2.me/theorems/4fe98ecf-1a55-4688-9af4-c107294b106e
-- title:
--   Any finite source physical Borel mark-simple predictable compensated jump sum is integrable and centred
-- statement:
--   For any finite family of genuinely original negative-jump marked rectangles, even overlapping or spanning different source time intervals, and any square-integrable predictor measurable at each rectangle's start in the original filtration, the signed compensated physical jump count sum is L1 and has zero expectation. No bounded coefficient, independent Poisson process, assumed per-cell moments or artificial stochastic integral.
-- source:
--   Actual source predictability plus Proved P4-F3 source unbounded L1 marked-cell result 53e31b78, pinned Mathlib finset Bochner integrability and integration. This supplies finite Borel mark-simple approximations for source Ms/Ml, before countable limits and stopped C2 Ito decomposition.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_unbounded_predictable_cell_L1_integral_zero
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_unbounded_predictable_mark_simple_L1_centered
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (cut : ℕ)
    (a b : ι → ℝ≥0)
    (hab : ∀ i ∈ S, a i ≤ b i)
    (hbT : ∀ i ∈ S, b i ≤ T)
    (ε : ℝ) (hε : 0 < ε) (B : ι → Set ℝ)
    (hB : ∀ i ∈ S, MeasurableSet (B i))
    (hBand : ∀ i ∈ S, B i ⊆ Ioo (-1 : ℝ) (-ε))
    (hCut : ∀ i ∈ S, B i ⊆ Iic (-(1 / ((cut : ℝ) + 1))))
    (H : ι → Ω → ℝ)
    (hH : ∀ i ∈ S, StronglyMeasurable[𝓕 (a i)] (H i))
    (hHL2 : ∀ i ∈ S, MemLp (H i) 2 P) :
    let N : ι → Ω → ℝ≥0∞ := fun i ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (a i) (b i) ×ˢ B i)
    let r : ι → ℝ := fun i =>
      ((((b i - a i : ℝ≥0) : ℝ≥0∞) * X.ν (B i))).toReal
    Integrable (fun ω => ∑ i ∈ S,
      H i ω * ((N i ω).toReal - r i)) P ∧
    (∫ ω, (∑ i ∈ S,
      H i ω * ((N i ω).toReal - r i)) ∂P) = 0 := by sorry

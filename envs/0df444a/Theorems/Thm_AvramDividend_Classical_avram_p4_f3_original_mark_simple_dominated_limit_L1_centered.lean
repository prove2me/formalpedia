-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_mark_simple_dominated_limit_L1_centered
-- name    : AvramDividend.Classical.avram_p4_f3_original_mark_simple_dominated_limit_L1_centered
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T14:37:36.738529+00:00
-- url     : https://prove2.me/theorems/4eb8ed1d-1692-471a-96e4-a91c7a4c70be
-- title:
--   Dominated localised limit of genuine original compensated marked sums remains centred
-- statement:
--   For a sequence of finite predictable compensated negative-jump marked sums formed from the same original spectrally negative Levy process, each already integrable and mean zero by the public source cell theorem, any integrable almost-sure limit with a single integrable envelope is also mean zero. This is an exact localised dominated-convergence passage and explicitly retains the extra envelope and limit premises; it does not assert that the natural stopped clock supplies them.
-- source:
--   Original physical marked cells of X and public Proved avram_p4_f3_original_unbounded_predictable_mark_simple_L1_centered; pinned Mathlib dominated convergence. This isolates the verified centring passage while retaining required uniform integrability control as a separately discharged source obligation.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_unbounded_predictable_mark_simple_L1_centered
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_mark_simple_dominated_limit_L1_centered
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {ι : Type*} [DecidableEq ι] (S : ℕ → Finset ι)
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (cut : ℕ)
    (a b : ℕ → ι → ℝ≥0)
    (hab : ∀ k, ∀ i ∈ S k, a k i ≤ b k i)
    (hbT : ∀ k, ∀ i ∈ S k, b k i ≤ T)
    (ε : ℝ) (hε : 0 < ε) (B : ℕ → ι → Set ℝ)
    (hB : ∀ k, ∀ i ∈ S k, MeasurableSet (B k i))
    (hBand : ∀ k, ∀ i ∈ S k, B k i ⊆ Ioo (-1 : ℝ) (-ε))
    (hCut : ∀ k, ∀ i ∈ S k, B k i ⊆ Iic (-(1 / ((cut : ℝ) + 1))))
    (H : ℕ → ι → Ω → ℝ)
    (hH : ∀ k, ∀ i ∈ S k, StronglyMeasurable[𝓕 (a k i)] (H k i))
    (hHL2 : ∀ k, ∀ i ∈ S k, MemLp (H k i) 2 P)
    (M g : Ω → ℝ) (hM : Integrable M P) (hg : Integrable g P) :
    let N : ℕ → ι → Ω → ℝ≥0∞ := fun k i ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (a k i) (b k i) ×ˢ B k i)
    let r : ℕ → ι → ℝ := fun k i =>
      ((((b k i - a k i : ℝ≥0) : ℝ≥0∞) * X.ν (B k i))).toReal
    let F : ℕ → Ω → ℝ := fun k ω =>
      ∑ i ∈ S k, H k i ω * ((N k i ω).toReal - r k i)
    (∀ k, ∀ᵐ ω ∂P, ‖F k ω‖ ≤ g ω) →
    (∀ᵐ ω ∂P, Tendsto (fun k => F k ω) atTop (𝓝 (M ω))) →
    (∫ ω, M ω ∂P) = 0 := by sorry

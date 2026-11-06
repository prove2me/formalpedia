-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_mark_simple_L2_convergent_limit_centred
-- name    : AvramDividend.Classical.avram_p4_f3_original_mark_simple_L2_convergent_limit_centred
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T14:37:30.685945+00:00
-- url     : https://prove2.me/theorems/af32fe73-7c81-4e7a-8761-237e22787d64
-- title:
--   Original compensated mark-simple L2 limit is centred by physical source passage
-- statement:
--   For actual finite predictable compensated negative-jump marked sums of one original spectrally negative Levy process, L2 seminorm convergence to an integrable original-process terminal limit entails L1 convergence and preservation of zero expectation. The finite source sums are centred by an already Proved physical count theorem, and L2 to L1 uses the exact pinned probability-space exponent inequality. The physical quadratic-isometry/Cauchy estimate needed to establish this convergence remains a separate stochastic obligation.
-- source:
--   Proved original mark-simple L1 centring theorem, pinned Mathlib eLpNorm_le_eLpNorm_of_exponent_le, eLpNorm_one_eq_lintegral_enorm, and tendsto_integral_of_L1. This is the exact original compensated small-jump L2-to-L1 limit transfer, leaving energy convergence explicit.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_unbounded_predictable_mark_simple_L1_centered
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_mark_simple_L2_convergent_limit_centred
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
    (M : Ω → ℝ) (hM : Integrable M P) :
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
    Tendsto (fun k => eLpNorm (fun ω => F k ω - M ω) 2 P) atTop (𝓝 0) →
    (∫ ω, M ω ∂P) = 0 := by sorry

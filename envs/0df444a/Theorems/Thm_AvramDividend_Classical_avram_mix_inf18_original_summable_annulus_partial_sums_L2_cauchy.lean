-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_inf18_original_summable_annulus_partial_sums_L2_cauchy
-- name    : AvramDividend.Classical.avram_mix_inf18_original_summable_annulus_partial_sums_L2_cauchy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T17:59:56.5192+00:00
-- url     : https://prove2.me/theorems/551cd8d6-c23d-40f0-bfb2-2a5d6c38959f
-- title:
--   Original physical compensated annulus partial sums are L2 Cauchy under finite variance energy
-- statement:
--   For the original physical negative-mark compensated jump counts, the actual partial sums of finite annulus coefficients are Cauchy in squared-integral mean when their deterministic variance-energy series is summable. The proof rewrites every difference of original partial sums as an exact shifted finite mark tail, handles either chronological index ordering, and imports the independently Proved uniform tail theorem 05728624. This provides an explicit L2 Cauchy premise for constructing the actual small-jump martingale limit, without positing a surrogate process or a stopped Ito-Meyer witness.
-- source:
--   MIX-INFINITE18 source-exact deterministic spatial-simple L2 Cauchy step towards 20281d57 represented compensated limit and original 5f12c023 stopped witness, then f5e6e083.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_inf18_original_summable_annulus_partial_sums_L2_cauchy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (cut : ℕ → ℕ) (hcut : Monotone cut) (a : ℕ → ℝ) :
    let B : ℕ → Set ℝ := fun i =>
      Ioc (-(1 / ((cut i : ℝ) + 1))) (-(1 / ((cut (i + 1) : ℝ) + 1)))
    let N : ℕ → Ω → ℝ≥0∞ := fun i ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B i)
    let r : ℕ → ℝ := fun i => ((T : ℝ≥0∞) * X.ν (B i)).toReal
    let Y : ℕ → Ω → ℝ := fun i ω => (N i ω).toReal - r i
    let S : ℕ → Ω → ℝ := fun n ω =>
      ∑ i ∈ Finset.range n, a i * Y i ω
    Summable (fun i => (a i) ^ 2 * r i) →
      ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
        ∀ n m : ℕ, n₀ ≤ n → n₀ ≤ m →
          Integrable (fun ω => (S n ω - S m ω) ^ 2) P ∧
          (∫ ω, (S n ω - S m ω) ^ 2 ∂P) < ε := by sorry

-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_inf17_original_summable_annulus_finite_tail_L2
-- name    : AvramDividend.Classical.avram_mix_inf17_original_summable_annulus_finite_tail_L2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T17:42:10.654199+00:00
-- url     : https://prove2.me/theorems/05728624-bb3d-4cbd-b430-ff5daedecdae
-- title:
--   Summable original compensated annulus energies give uniform finite-tail L2 smallness
-- statement:
--   For arbitrary finite chronologically original jump annulus step sums, if the deterministic spatial coefficients have summable exact compensated variance energy, then all sufficiently late finite annulus tails have uniformly small L2 energy. This is an original-process small-jump finite-tail Cauchy estimate derived from the genuine proven arbitrary finite orthogonal annulus isometry and the summability of the deterministic rate series. It does not yet identify the source stochastic integral with a predictable stopped Itô-Meyer integral; Gaussian residual and dividend/ruin ledger remain open.
-- source:
--   MIX-INFINITE17 original deterministic finite spatial simple mark L2 small-jump approximation towards 5f12c023 -> f5e6e083 -> 6e72d9ed. Uses authoritatively Proved 0af54511, with no extra L2 source axioms.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_inf17_original_summable_annulus_finite_tail_L2
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
    Summable (fun i => (a i) ^ 2 * r i) →
      ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ k : ℕ,
        Integrable (fun ω =>
          (∑ i ∈ Finset.range k, a (n + i) * Y (n + i) ω) ^ 2) P ∧
        (∫ ω, (∑ i ∈ Finset.range k,
          a (n + i) * Y (n + i) ω) ^ 2 ∂P) < ε := by sorry

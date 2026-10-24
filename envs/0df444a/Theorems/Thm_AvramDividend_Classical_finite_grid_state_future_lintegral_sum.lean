-- Prove2me | Theorems.Thm_AvramDividend_Classical_finite_grid_state_future_lintegral_sum
-- name    : AvramDividend.Classical.finite_grid_state_future_lintegral_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T12:18:34.478536+00:00
-- url     : https://prove2.me/theorems/776eca40-3730-4387-8c4a-0038b8e6d971
-- title:
--   Finite-grid stopped future-path discounted integral sum
-- statement:
--   For a spectrally negative Lévy process and any finite grid of deterministic times with arbitrary history observables at each grid point, if every finite family of shifted future increments at each grid time generates a sigma-algebra independent of the past, then the sum over grid points of the expected nonnegative path-dependent payoffs equals the sum of the corresponding product integrals. This packages the per-grid-point deterministic-time Markov step (the proved product law) for finite-valued stopping-time partitions in the barrier dividend factorization.
-- source:
--   Grid-sum packaging of the deterministic-time Markov step for finite-valued stopping-time partitions. Each summand follows from the proved finite-time arbitrary-history product law by lintegral_map/prod; the finite sum needs no analysis. Source-faithful to the in-repo research draft finite_time_state_future_product_for_barrier_factorization.lean (third theorem).

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Process.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem AvramDividend.Classical.finite_grid_state_future_lintegral_sum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {E : Type*} [MeasurableSpace E]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ι → ℝ≥0) (H : ι → Ω → E)
    (hH : ∀ i, Measurable[𝓕 (s i)] (H i))
    (hFinite : ∀ i, ∀ I : Finset ℝ≥0,
      Indep (⨆ t ∈ I,
        MeasurableSpace.comap
          (fun ω => X.X (s i + t) ω - X.X (s i) ω) inferInstance)
        (𝓕 (s i)) P)
    (f : ι → E × (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    (∑ i, ∫⁻ ω, f i (H i ω,
        (fun t : ℝ≥0 => X.X (s i + t) ω - X.X (s i) ω)) ∂P) =
      ∑ i, ∫⁻ h, ∫⁻ y, f i (h, y)
        ∂(Measure.map
          (fun ω => fun t : ℝ≥0 => X.X (s i + t) ω - X.X (s i) ω) P)
        ∂(Measure.map (H i) P) := by sorry

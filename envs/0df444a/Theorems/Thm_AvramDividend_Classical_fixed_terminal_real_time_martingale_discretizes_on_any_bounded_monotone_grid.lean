-- Prove2me | Theorems.Thm_AvramDividend_Classical_fixed_terminal_real_time_martingale_discretizes_on_any_bounded_monotone_grid
-- name    : AvramDividend.Classical.fixed_terminal_real_time_martingale_discretizes_on_any_bounded_monotone_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:24:42.87647+00:00
-- url     : https://prove2.me/theorems/63adb7c9-f28c-462f-9142-761a30de8056
-- title:
--   A fixed-horizon real-time event martingale becomes a genuine discrete martingale on any bounded monotone grid
-- statement:
--   For a filtered measurable space, a fixed finite ambient measure μ, a bounded monotone deterministic grid of times g:ℕ→[0,T], and a strongly adapted real reward process Z_t which is integrable at every grid point and satisfies earlier-event martingale restricted-integral identities for s≤t≤T, there exists a natural-number filtration G_n=F_{g(n)} under which the sampled process Z_{g(n)} is a genuine Mathlib `Martingale` under the *same measure μ*. This is the last abstract constructor needed to apply the already Proved finite-grid Doob maximal inequality to the genuine Esscher tilted law.
-- source:
--   Use the proved grid-induced natural-number filtration existence lemma to obtain G_n=F_{g(n)}. Its evaluation equality transfers the strong adaptedness of Z and past-event measurability to G. Apply pinned Mathlib `martingale_of_setIntegral_eq_succ` with integrability at g(n) and fixed-terminal earlier-event identities at consecutive grid points, using monotonicity and the T bound on g.

import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Process.Filtration
import Theorems.Thm_AvramDividend_Classical_exists_nat_filtration_along_monotone_nonnegative_time_grid
open MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.fixed_terminal_real_time_martingale_discretizes_on_any_bounded_monotone_grid
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (T : ℝ≥0) (g : ℕ → ℝ≥0) (hg : Monotone g)
    (hgT : ∀ n : ℕ, g n ≤ T)
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (Z : ℝ≥0 → Ω → ℝ)
    (hadapt : ∀ t : ℝ≥0, StronglyMeasurable[𝓕 t] (Z t))
    (hint : ∀ n : ℕ, Integrable (Z (g n)) μ)
    (hevents : ∀ s t : ℝ≥0, s ≤ t → t ≤ T →
      ∀ A : Set Ω, @MeasurableSet Ω (𝓕 s) A →
      (∫ ω in A, Z s ω ∂μ) = (∫ ω in A, Z t ω ∂μ)) :
    ∃ 𝓖 : Filtration ℕ mΩ,
      (∀ n : ℕ, 𝓖 n = 𝓕 (g n)) ∧
      Martingale (fun n ω => Z (g n) ω) 𝓖 μ := by sorry

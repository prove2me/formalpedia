-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_antitone_powers_quadratic_pointwise_of_measurable_recursion
-- name    : AvramDividend.Classical.causal_antitone_powers_quadratic_pointwise_of_measurable_recursion
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T15:03:17.720983+00:00
-- url     : https://prove2.me/theorems/0f6ad4fd-8458-4a4a-92a9-98250e0239a0
-- title:
--   Quadratic-geometric antitone causal power bound from measurable L1 recursion
-- statement:
--   For nonnegative antitone causal L1 kernels and recursively defined nonnegative L1 convolution powers with geometric mass bound, the pointwise quadratic-geometric estimate follows from a simultaneous induction that also establishes every split-product interval integrability condition. No global boundedness of the kernel near zero is assumed. The only extra analytic premises beyond L1 integrability are the explicit restricted-factor ae strong measurability properties needed by the split-product theorem.
-- source:
--   Simultaneous induction on causal powers. The inductive pointwise bound controls right-factor essential norm; antitonicity controls the left reflected kernel; published split-product integrability follows; published quadratic successor then gives the next pointwise bound.

import Mathlib.Analysis.Convolution
import Theorems.Thm_AvramDividend_Classical_causal_neumann_quadratic_convolution_successor_bound
import Theorems.Thm_AvramDividend_Classical_causal_reflected_kernel_right_interval_integrable
import Theorems.Thm_AvramDividend_Classical_causal_antitone_split_product_integrable_of_pointwise_bound

open MeasureTheory Set

theorem AvramDividend.Classical.causal_antitone_powers_quadratic_pointwise_of_measurable_recursion
    (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ) (ρ : ℝ)
    (hρ : 0 ≤ ρ) (hanti : AntitoneOn κ (Ioi (0 : ℝ)))
    (hKpoint : ∀ x : ℝ, 0 < x → κ x ≤ ρ / x)
    (hKnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ κ t)
    (hKint : ∀ y : ℝ, 0 < y → IntervalIntegrable κ volume 0 y)
    (hKmass : ∀ y : ℝ, 0 < y → (∫ t in (0 : ℝ)..y, κ t) ≤ ρ)
    (hzero : F 0 = κ)
    (hsucc : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x →
      F (n + 1) x = ∫ s in Ioc (0 : ℝ) x, κ (x - s) * F n s ∂volume)
    (hFnonneg : ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → 0 ≤ F n t)
    (hFint : ∀ n : ℕ, ∀ u : ℝ, 0 ≤ u → IntervalIntegrable (F n) volume 0 u)
    (hFmass : ∀ n : ℕ, ∀ u : ℝ, 0 ≤ u →
      (∫ s in (0 : ℝ)..u, F n s) ≤ ρ ^ (n + 1))
    (hKleftMeas : ∀ x u : ℝ, 0 < u → u < x →
      AEStronglyMeasurable (fun s : ℝ => κ (x - s))
        (volume.restrict (Ioc (0 : ℝ) u)))
    (hFrightMeas : ∀ n : ℕ, ∀ x u : ℝ, 0 < u → u < x →
      AEStronglyMeasurable (F n) (volume.restrict (Ioc u x))) :
    ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      F n x ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x := by sorry

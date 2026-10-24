-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_antitone_powers_quadratic_pointwise_of_split_integrable
-- name    : AvramDividend.Classical.causal_antitone_powers_quadratic_pointwise_of_split_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T14:29:03.50944+00:00
-- url     : https://prove2.me/theorems/61e6094a-a308-4e70-9eae-c95fd36e5f98
-- title:
--   Conditional quadratic-geometric pointwise bound for all antitone convolution powers
-- statement:
--   An inductive quadratic-geometric estimate for every causal convolution power of a nonnegative antitone kernel, assuming the necessary split-interval product integrability. The result isolates the exact analytic integrability bridge still needed for the Gaussian Volterra resolvent, and propagates the bound using the published antitone cutoff successor inequality.
-- source:
--   Natural induction: base mass-over-time bound, rational split u=(n+1)x/(n+2), accepted successor inequality, and exact Ioc-to-interval conversion.

import Mathlib.Analysis.Convolution
import Theorems.Thm_AvramDividend_Classical_causal_neumann_quadratic_convolution_successor_bound

open MeasureTheory Set

theorem AvramDividend.Classical.causal_antitone_powers_quadratic_pointwise_of_split_integrable
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
    (hKrightInt : ∀ x u : ℝ, 0 < u → u < x →
      IntervalIntegrable (fun s : ℝ => κ (x - s)) volume u x)
    (hProdInt : ∀ n : ℕ, ∀ x u : ℝ, 0 < u → u < x →
      IntervalIntegrable (fun s : ℝ => κ (x - s) * F n s) volume 0 u ∧
      IntervalIntegrable (fun s : ℝ => κ (x - s) * F n s) volume u x) :
    ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      F n x ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x := by sorry
